use itertools::Itertools;
use std::marker::PhantomData;
use strum::IntoEnumIterator;

use crate::table::LookupTable;
use crate::{
    evm_circuit::{
        param::{
            BLOCK_TABLE_LOOKUPS, BYTECODE_TABLE_LOOKUPS, COPY_TABLE_LOOKUPS, EVM_LOOKUP_COLS,
            EXP_TABLE_LOOKUPS, FIXED_TABLE_LOOKUPS, KECCAK_TABLE_LOOKUPS, MAX_STEP_HEIGHT,
            N_BYTE_LOOKUPS, N_COPY_COLUMNS, N_PHASE1_COLUMNS, N_PHASE2_COLUMNS, RW_TABLE_LOOKUPS,
            STEP_WIDTH, TX_TABLE_LOOKUPS,
        },
        step::{ExecutionState, Step},
        table::{FixedTableTag, Table},
        util::{
            constraint_builder::ConstraintBuilder, rlc, CachedRegion, CellType, Expr,
            StoredExpression, LOOKUP_CONFIG,
        },
        Advice, Column, Fixed,
    },
    util::Challenges,
};
use eth_types::{Field, Word, U256};
pub(crate) use halo2_proofs::circuit::{Layouter, Region, Value};
use halo2_proofs::plonk::{FirstPhase, SecondPhase, ThirdPhase};
use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    dev::MockProver,
    plonk::{Circuit, ConstraintSystem, Error, Expression, Selector},
};

pub(crate) const WORD_LOW_MAX: Word = U256([u64::MAX, u64::MAX, 0, 0]);
pub(crate) const WORD_HIGH_MAX: Word = U256([0, 0, u64::MAX, u64::MAX]);
// Maximum field value in bn256: bn256::MODULES - 1
pub(crate) const WORD_CELL_MAX: Word = U256([
    0x43e1f593f0000000,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

// I256::MAX = 2^255 - 1, and I256::MIN = 2^255.
pub(crate) const WORD_SIGNED_MAX: Word = U256([u64::MAX, u64::MAX, u64::MAX, i64::MAX as _]);
pub(crate) const WORD_SIGNED_MIN: Word = U256([0, 0, 0, i64::MIN as _]);

pub(crate) fn generate_power_of_randomness<F: Field>(randomness: F) -> Vec<F> {
    (1..32).map(|exp| randomness.pow(&[exp, 0, 0, 0])).collect()
}

pub trait MathGadgetContainer<F: Field>: Clone {
    fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self
    where
        Self: Sized;

    fn assign_gadget_container(
        &self,
        witnesses: &[Word],
        region: &mut CachedRegion<'_, '_, F>,
    ) -> Result<(), Error>;
}

#[derive(Debug, Clone)]
pub struct UnitTestMathGadgetBaseCircuitConfig<F: Field, G>
where
    G: MathGadgetContainer<F>,
{
    q_usable: Selector,
    fixed_table: [Column<Fixed>; 4],
    byte_table: [Column<Fixed>; 1],
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    stored_expressions: Vec<StoredExpression<F>>,
    math_gadget_container: G,
    _marker: PhantomData<F>,
    challenges: Challenges<Expression<F>>,
}

impl<F: Field, G> UnitTestMathGadgetBaseCircuitConfig<F, G>
where
    G: MathGadgetContainer<F>,
{
    fn annotate_circuit(&self, region: &mut Region<F>) {
        let groups = [
            ("lf", FIXED_TABLE_LOOKUPS),
            ("ltx", TX_TABLE_LOOKUPS),
            ("lrw", RW_TABLE_LOOKUPS),
            ("lby", BYTECODE_TABLE_LOOKUPS),
            ("lbl", BLOCK_TABLE_LOOKUPS),
            ("lco", COPY_TABLE_LOOKUPS),
            ("lke", KECCAK_TABLE_LOOKUPS),
            ("lex", EXP_TABLE_LOOKUPS),
            ("y", N_PHASE2_COLUMNS),
            ("cp", N_COPY_COLUMNS),
            ("b", N_BYTE_LOOKUPS),
            ("x", N_PHASE1_COLUMNS),
        ];
        let groups: Vec<_> = groups.iter().filter(|(name, length)| *length > 0).collect();
        let mut group_index = 0;
        let mut index = 0;
        for col in self.advices {
            let (name, length) = groups[group_index];
            region.name_column(|| format!("{}{}", name, index), col);
            index += 1;
            if index >= *length {
                index = 0;
                group_index += 1;
            }
        }
    }
}

pub struct UnitTestMathGadgetBaseCircuit<G> {
    size: usize,
    witnesses: Vec<Word>,
    _marker: PhantomData<G>,
}

impl<G> UnitTestMathGadgetBaseCircuit<G> {
    pub fn new(size: usize, witnesses: Vec<Word>) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size,
            witnesses,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, G: MathGadgetContainer<F>> Circuit<F> for UnitTestMathGadgetBaseCircuit<G> {
    type Config = (UnitTestMathGadgetBaseCircuitConfig<F, G>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size: 0,
            witnesses: vec![],
            _marker: PhantomData,
        }
    }

    fn configure(&self, meta: &mut ConstraintSystem<F>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenges_exprs = challenges.exprs(meta);

        let q_usable = meta.selector();
        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let byte_table = [(); 1].map(|_| meta.fixed_column());
        meta.annotate_lookup_any_column(byte_table[0], || "u8");

        let lookup_column_count: usize = LOOKUP_CONFIG.iter().map(|(_, count)| *count).sum();
        let advices = [(); STEP_WIDTH]
            .iter()
            .enumerate()
            .map(|(n, _)| {
                if n < lookup_column_count {
                    meta.advice_column_in(ThirdPhase)
                } else if n < lookup_column_count + N_PHASE2_COLUMNS {
                    meta.advice_column_in(SecondPhase)
                } else {
                    meta.advice_column_in(FirstPhase)
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let step_curr = Step::new(meta, advices, 0, false);
        let step_next = Step::new(meta, advices, MAX_STEP_HEIGHT, true);
        let mut cb = ConstraintBuilder::new(
            step_curr.clone(),
            step_next,
            &challenges_exprs,
            ExecutionState::STOP,
        );
        let math_gadget_container = G::configure_gadget_container(&mut cb);
        let (constraints, stored_expressions, query_names, _) = cb.build_query_names();

        if !constraints.step.is_empty() {
            let step_constraints = constraints.step;
            meta.create_gate("MathGadgetTestContainer", |meta| {
                let q_usable = meta.query_selector(q_usable);
                meta.push_query_names(q_usable.clone(), step_curr.query_names());
                meta.push_query_names(query_names.0, query_names.1);
                step_constraints
                    .into_iter()
                    .map(move |(name, constraint)| (name, q_usable.clone() * constraint))
            });
        }

        let cell_manager = step_curr.cell_manager.clone();
        for column in cell_manager.columns().iter() {
            if let CellType::Lookup(table) = column.cell_type {
                if table == Table::Fixed {
                    let name = format!("{:?}", table);
                    meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                        let table_expressions = fixed_table.table_exprs(meta);
                        vec![(
                            column.expr(),
                            rlc::expr(&table_expressions, challenges_exprs.lookup_input()),
                        )]
                    });
                }
            }
            if let CellType::LookupByte = column.cell_type {
                meta.lookup_any("Byte lookup", |meta| {
                    let byte_table_expression = byte_table.table_exprs(meta)[0].clone();
                    vec![(column.expr(), byte_table_expression)]
                });
            }
        }

        (
            UnitTestMathGadgetBaseCircuitConfig::<F, G> {
                q_usable,
                fixed_table,
                byte_table,
                advices,
                step: step_curr,
                stored_expressions,
                math_gadget_container,
                _marker: PhantomData,
                challenges: challenges_exprs,
            },
            challenges,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let (config, challenges) = config;
        let challenge_values = challenges.values(&mut layouter);
        layouter.assign_region(
            || "assign test container",
            |mut region| {
                config.annotate_circuit(&mut region);
                let offset = 0;
                config.q_usable.enable(&mut region, offset)?;
                let cached_region = &mut CachedRegion::<'_, '_, F>::new(
                    &mut region,
                    &challenge_values,
                    config.advices.to_vec(),
                    MAX_STEP_HEIGHT * 3,
                    offset,
                );
                config.step.state.execution_state.assign(
                    cached_region,
                    offset,
                    ExecutionState::STOP as usize,
                )?;
                config
                    .math_gadget_container
                    .assign_gadget_container(&self.witnesses, cached_region)?;
                for stored_expr in &config.stored_expressions {
                    stored_expr.assign(cached_region, offset)?;
                }
                Ok(())
            },
        )?;

        // assign fixed range tables only as they are the only tables referred by a
        // specfic math gadget -- ConstantDivisionGadget.
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 4])
                    .chain(
                        FixedTableTag::iter()
                            .filter(|t| {
                                matches!(
                                    t,
                                    FixedTableTag::Range5
                                        | FixedTableTag::Range16
                                        | FixedTableTag::Range32
                                        | FixedTableTag::Range64
                                        | FixedTableTag::Range128
                                        | FixedTableTag::Range256
                                        | FixedTableTag::Range512
                                        | FixedTableTag::Range1024
                                )
                            })
                            .flat_map(|tag| tag.build()),
                    )
                    .enumerate()
                {
                    for (column, value) in config.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                    }
                }

                Ok(())
            },
        )?;

        // Load byte table
        layouter.assign_region(
            || "byte table",
            |mut region| {
                for offset in 0..256 {
                    region.assign_fixed(
                        || "",
                        config.byte_table[0],
                        offset,
                        || Value::known(F::from(offset as u64)),
                    )?;
                }

                Ok(())
            },
        )
    }
}

/// This fn test_math_gadget_container takes math gadget container and run a
/// container based circuit. All test logic should be included in the container,
/// and witness words are used for both input & output data. How to deal with
/// the witness words is left to each container.
pub(crate) fn test_math_gadget_container<F: Field, G: MathGadgetContainer<F>>(
    witnesses: Vec<Word>,
    expected_success: bool,
) {
    const K: usize = 12;
    let circuit = UnitTestMathGadgetBaseCircuit::<G>::new(K, witnesses);

    let prover = MockProver::<F>::run(K as u32, &circuit, vec![]).unwrap();
    if expected_success {
        assert_eq!(prover.verify(), Ok(()));
    } else {
        assert_ne!(prover.verify(), Ok(()));
    }
}

/// A simple macro for less code & better readability
#[cfg(test)]
macro_rules! try_test {
    ($base_class:ty, $witnesses:expr, $expect_success:expr $(,)?) => {{
        test_math_gadget_container::<Fr, $base_class>($witnesses.to_vec(), $expect_success)
    }};
}

#[cfg(test)]
pub(crate) use try_test;
