use crate::{ENDIANNESS_PIVOT_GKR, prove_gkr_quotient, verify_gkr_quotient};
use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::ansi::Colorize;
use utils::*;

#[derive(Debug, PartialEq, Hash, Clone)]
pub struct GenericLogupStatements {
    pub memory_and_acc_point: MultilinearPoint<EF>,
    pub value_memory: EF,
    pub value_memory_acc: EF,
    pub bytecode_and_acc_point: MultilinearPoint<EF>,
    pub value_bytecode_acc: EF,
    pub bus_numerators_values: BTreeMap<Table, EF>,
    pub bus_denominators_values: BTreeMap<Table, EF>,
    pub gkr_point: Vec<EF>,
    pub columns_values: BTreeMap<Table, BTreeMap<ColIndex, EF>>,
    // Used in recursion
    pub total_gkr_n_vars: usize,
    pub bytecode_evaluation: Option<Evaluation<EF>>,
}

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all)]
pub fn prove_generic_logup(
    prover_state: &mut impl FSProver<EF>,
    c: EF,
    alphas_eq_poly: &[EF],
    memory: &[F],
    memory_acc: &[F],
    bytecode_multilinear: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> GenericLogupStatements {
    assert!(memory.len().is_power_of_two());
    assert_eq!(memory.len(), memory_acc.len());
    assert!(memory.len() >= traces.values().map(|t| 1 << t.log_n_rows).max().unwrap());

    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let tables_log_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_log_heights_sorted = sort_tables_by_height(&tables_log_heights);

    let total_active_len = compute_total_active_len(
        log2_strict_usize(memory.len()),
        log_bytecode,
        &tables_log_heights_sorted,
    );
    let total_gkr_n_vars = log2_ceil_usize(total_active_len);
    let mut numerators: Vec<F> = unsafe { uninitialized_vec(total_active_len) };
    let width = packing_width::<EF>();
    let mut denominators: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(total_active_len / width) };
    let c_packed = EFPacking::<EF>::from(c);
    let alphas_packed: Vec<EFPacking<EF>> = alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
    let memory_domainsep_packed = PFPacking::<EF>::from(F::from_usize(LOGUP_MEMORY_DOMAINSEP));
    let bytecode_domainsep_packed = PFPacking::<EF>::from(F::from_usize(LOGUP_BYTECODE_DOMAINSEP));

    let min_section_log = log_bytecode.min(tables_log_heights_sorted.last().unwrap().1);
    if min_section_log < ENDIANNESS_PIVOT_GKR {
        tracing::info!("TODO: suboptimal GKR pivot (could be improved).");
    }
    let pivot = ENDIANNESS_PIVOT_GKR.min(min_section_log);
    let chunk_size = 1usize << pivot;
    let chunk_shift = usize::BITS as usize - pivot;
    let chunk_mask = chunk_size - 1;
    let max_table_height = 1 << tables_log_heights_sorted[0].1;

    let src_idx = |p: usize, w: usize| -> usize {
        let x = p * width + w;
        (x & !chunk_mask) | ((x & chunk_mask).reverse_bits() >> chunk_shift)
    };

    let fill_num_from = |dst: &mut [F], src: &[F], neg: bool| {
        dst.par_chunks_exact_mut(chunk_size)
            .enumerate()
            .for_each(|(c, dst_chunk)| {
                let src_chunk = &src[c * chunk_size..][..chunk_size];
                for (i, slot) in dst_chunk.iter_mut().enumerate() {
                    let v = src_chunk[i.reverse_bits() >> chunk_shift];
                    *slot = if neg { -v } else { v };
                }
            });
    };

    let mut offset = 0;

    // Memory section.
    assert_eq!(memory.len(), memory_acc.len());
    fill_num_from(&mut numerators[offset..][..memory.len()], memory_acc, true);
    fill_denoms(&mut denominators[offset / width..][..memory.len() / width], |p| {
        c_packed
            - finger_print_packed::<EF>(
                memory_domainsep_packed,
                &[
                    PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w))),
                    PFPacking::<EF>::from_fn(|w| memory[src_idx(p, w)]),
                ],
                &alphas_packed,
            )
    });
    offset += memory.len();

    // Bytecode section.
    assert_eq!(1 << log_bytecode, bytecode_acc.len());
    fill_num_from(&mut numerators[offset..][..bytecode_acc.len()], bytecode_acc, true);
    let bytecode_stride = N_INSTRUCTION_COLUMNS.next_power_of_two();
    fill_denoms(
        &mut denominators[offset / width..][..(1 << log_bytecode) / width],
        |p| {
            let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
            for k in 0..N_INSTRUCTION_COLUMNS {
                data[k] = PFPacking::<EF>::from_fn(|w| bytecode_multilinear[src_idx(p, w) * bytecode_stride + k]);
            }
            data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w)));
            c_packed - finger_print_packed::<EF>(bytecode_domainsep_packed, &data, &alphas_packed)
        },
    );
    if 1 << log_bytecode < max_table_height {
        // padding
        numerators[offset + (1 << log_bytecode)..offset + max_table_height]
            .par_iter_mut()
            .for_each(|n| *n = F::ZERO);
        denominators[(offset + (1 << log_bytecode)) / width..(offset + max_table_height) / width]
            .par_iter_mut()
            .for_each(|d| *d = EFPacking::<EF>::ONE);
    }
    offset += max_table_height.max(1 << log_bytecode);

    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;
        let buses = table.bus_interactions();
        let mem_groups = memory_lookup_groups(&buses);

        let mut next_group = 0;
        let mut bus_idx = 0;
        while bus_idx < buses.len() {
            if next_group < mem_groups.len() && mem_groups[next_group].start_bus == bus_idx {
                let group = &mem_groups[next_group];
                let group_len = group.value_cols.len();
                let col_index = &trace.columns[group.idx_col];
                let packed_chunk_size = (1 << log_n_rows) / width;

                numerators[offset..][..group_len << log_n_rows]
                    .par_iter_mut()
                    .for_each(|n| *n = F::ONE);

                denominators[offset / width..][..group_len * packed_chunk_size]
                    .par_chunks_exact_mut(packed_chunk_size)
                    .enumerate()
                    .for_each(|(i, denom_chunk)| {
                        let i_field = F::from_usize(i);
                        let col_value = &trace.columns[group.value_cols[i]];
                        denom_chunk.par_iter_mut().enumerate().for_each(|(p, slot)| {
                            *slot = c_packed
                                - finger_print_packed::<EF>(
                                    memory_domainsep_packed,
                                    &[
                                        PFPacking::<EF>::from_fn(|w| col_index[src_idx(p, w)] + i_field),
                                        PFPacking::<EF>::from_fn(|w| col_value[src_idx(p, w)]),
                                    ],
                                    &alphas_packed,
                                );
                        });
                    });
                offset += group_len << log_n_rows;
                bus_idx += group_len;
                next_group += 1;
                continue;
            }

            let bus = &buses[bus_idx];
            let slice = &mut numerators[offset..][..1 << log_n_rows];
            match bus.multiplicity {
                BusMultiplicity::One => {
                    let val = bus.direction.to_field_flag();
                    slice.par_iter_mut().for_each(|n| *n = val);
                }
                BusMultiplicity::Column(col) => {
                    fill_num_from(slice, &trace.columns[col], matches!(bus.direction, BusDirection::Pull));
                }
            }
            let denom_slot = &mut denominators[offset / width..][..(1 << log_n_rows) / width];

            let n_data = bus.data.len();
            let mut data_cols: [&[F]; MAX_BUS_WIDTH] = [&[]; MAX_BUS_WIDTH];
            for (k, entry) in bus.data.iter().enumerate() {
                match *entry {
                    BusData::Column(c) => {
                        data_cols[k] = &trace.columns[c];
                    }
                    _ => {
                        panic!("Non-Column BusData::data entries are not supported on the fast path");
                    }
                }
            }
            let ds_col: Option<&[F]> = match bus.domainsep {
                BusData::Column(c) => Some(&trace.columns[c]),
                _ => None,
            };
            let ds_constant_packed: PFPacking<EF> = match bus.domainsep {
                BusData::Constant(v) => PFPacking::<EF>::from(F::from_usize(v)),
                _ => PFPacking::<EF>::ZERO,
            };

            fill_denoms(denom_slot, |p| {
                let mut data_buf = [PFPacking::<EF>::ZERO; MAX_BUS_WIDTH];
                for k in 0..n_data {
                    let col = data_cols[k];
                    data_buf[k] = PFPacking::<EF>::from_fn(|w| col[src_idx(p, w)]);
                }
                let ds = match ds_col {
                    Some(col) => PFPacking::<EF>::from_fn(|w| col[src_idx(p, w)]),
                    None => ds_constant_packed,
                };
                c_packed - finger_print_packed::<EF>(ds, &data_buf[..n_data], &alphas_packed)
            });
            offset += 1 << log_n_rows;
            bus_idx += 1;
        }
    }

    assert_eq!(offset, total_active_len);
    tracing::info!(
        "{}",
        format!(
            "Logup data: {} = 2^{} * (1 + {:.2})",
            offset,
            total_gkr_n_vars - 1,
            (offset as f64) / (1 << (total_gkr_n_vars - 1)) as f64 - 1.0
        )
        .blue()
    );

    let (sum, claim_point_gkr) = prove_gkr_quotient::<EF>(
        prover_state,
        PFPacking::<EF>::pack_slice(&numerators),
        &denominators,
        pivot,
    );

    // sanity check
    assert_eq!(sum, EF::ZERO);

    // Memory: ...
    let memory_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log2_strict_usize(memory.len())).to_vec());
    let value_memory_acc = memory_acc.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory_acc);

    let value_memory = memory.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory);

    let bytecode_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log_bytecode).to_vec());
    let value_bytecode_acc = bytecode_acc.evaluate(&bytecode_and_acc_point);
    prover_state.add_extension_scalar(value_bytecode_acc);

    // evaluation on bytecode itself can be done directly by the verifier

    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    for table in ALL_TABLES {
        let trace = &traces[&table];
        let log_n_rows = trace.log_n_rows;

        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        let resolve_ef = |entry: BusData| -> EF {
            match entry {
                BusData::Column(col) => trace.columns[col].evaluate(&inner_point),
                BusData::ColumnPlusConstant(col, ofs) => trace.columns[col].evaluate(&inner_point) + F::from_usize(ofs),
                BusData::Constant(val) => EF::from_usize(val),
            }
        };

        for bus in table.bus_interactions() {
            match bus.multiplicity {
                BusMultiplicity::Column(mult_col) => {
                    let eval_on_multiplicity =
                        trace.columns[mult_col].evaluate(&inner_point) * bus.direction.to_field_flag();
                    prover_state.add_extension_scalar(eval_on_multiplicity);
                    let data_evals: Vec<EF> = bus.data.iter().map(|e| resolve_ef(*e)).collect();
                    let eval_on_data = c - finger_print(resolve_ef(bus.domainsep), &data_evals, alphas_eq_poly);
                    prover_state.add_extension_scalar(eval_on_data);
                    bus_numerators_values.insert(table, eval_on_multiplicity);
                    bus_denominators_values.insert(table, eval_on_data);
                }
                BusMultiplicity::One => {
                    // Skip columns already in table_values: memory-lookup groups share
                    // an idx column across buses, so it's written once per group rather
                    // than once per bus. This also keeps simple-lookup writes (e.g. the
                    // bytecode bus) batched into a single RATE-aligned transcript block.
                    let col_evals: Vec<EF> = bus
                        .data
                        .iter()
                        .filter_map(|entry| {
                            entry.column().and_then(|col| {
                                if let std::collections::btree_map::Entry::Vacant(e) = table_values.entry(col) {
                                    let v = trace.columns[col].evaluate(&inner_point);
                                    e.insert(v);
                                    Some(v)
                                } else {
                                    None
                                }
                            })
                        })
                        .collect();
                    prover_state.add_extension_scalars(&col_evals);
                }
            }
        }

        columns_values.insert(table, table_values);
    }

    GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        gkr_point: claim_point_gkr.0,
        columns_values,
        total_gkr_n_vars,
        bytecode_evaluation: None,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn verify_generic_logup(
    verifier_state: &mut impl FSVerifier<EF>,
    c: EF,
    alphas: &[EF],
    alphas_eq_poly: &[EF],
    log_memory: usize,
    bytecode_multilinear: &[F],
    table_log_n_rows: &BTreeMap<Table, VarCount>,
) -> ProofResult<GenericLogupStatements> {
    let tables_heights_sorted = sort_tables_by_height(table_log_n_rows);
    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let total_gkr_n_vars = compute_total_logup_log_size(log_memory, log_bytecode, &tables_heights_sorted);

    let (sum, point_gkr, numerators_value, denominators_value) = verify_gkr_quotient(verifier_state, total_gkr_n_vars)?;

    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;

    let pref_at = |offset: usize, log_height: usize| {
        let n_missing = total_gkr_n_vars - log_height;
        let bits = to_big_endian_in_field::<EF>(offset >> log_height, n_missing);
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(point_gkr[..n_missing].to_vec()))
    };

    let memory_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_memory).to_vec());
    let pref = pref_at(0, log_memory);

    let value_memory_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_memory_acc;

    let value_memory = verifier_state.next_extension_scalar()?;
    let value_index = mle_of_01234567_etc(&memory_and_acc_point);
    retrieved_denominators_value += pref
        * (c - finger_print(
            EF::from_usize(LOGUP_MEMORY_DOMAINSEP),
            &[value_index, value_memory],
            alphas_eq_poly,
        ));
    let mut offset = 1 << log_memory;

    let log_bytecode_padded = log_bytecode.max(tables_heights_sorted[0].1);
    let bytecode_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_bytecode).to_vec());
    let pref = pref_at(offset, log_bytecode);
    let pref_padded = pref_at(offset, log_bytecode_padded);

    let value_bytecode_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_bytecode_acc;

    // Bytecode denominator - computed directly by verifier
    let bytecode_index_value = mle_of_01234567_etc(&bytecode_and_acc_point);

    let mut bytecode_point = bytecode_and_acc_point.0.clone();
    bytecode_point.extend(from_end(alphas, log2_ceil_usize(N_INSTRUCTION_COLUMNS)));
    let bytecode_point = MultilinearPoint(bytecode_point);
    let bytecode_value = bytecode_multilinear.evaluate(&bytecode_point);
    let bytecode_value_corrected = bytecode_value
        * alphas[..alphas.len() - log2_ceil_usize(N_INSTRUCTION_COLUMNS)]
            .iter()
            .map(|x| EF::ONE - *x)
            .product::<EF>();
    retrieved_denominators_value += pref
        * (c - (bytecode_value_corrected
            + bytecode_index_value * alphas_eq_poly[N_INSTRUCTION_COLUMNS]
            + *alphas_eq_poly.last().unwrap() * F::from_usize(LOGUP_BYTECODE_DOMAINSEP)));
    // Padding for bytecode
    retrieved_denominators_value +=
        pref_padded * mle_of_zeros_then_ones(1 << log_bytecode, from_end(&point_gkr, log_bytecode_padded));
    offset += 1 << log_bytecode_padded;

    // ... Rest of the tables.
    let mut layout_offsets: BTreeMap<Table, usize> = BTreeMap::new();
    let mut layout_offset = offset;
    for &(table, log_n_rows) in &tables_heights_sorted {
        layout_offsets.insert(table, layout_offset);
        layout_offset += offset_for_table(&table, log_n_rows);
    }
    let final_offset = layout_offset;

    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    for table in ALL_TABLES {
        let log_n_rows = table_log_n_rows[&table];
        let mut offset_within_table = layout_offsets[&table];
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        for bus in table.bus_interactions() {
            let pref = pref_at(offset_within_table, log_n_rows);
            match bus.multiplicity {
                BusMultiplicity::Column(_) => {
                    let eval_on_multiplicity = verifier_state.next_extension_scalar()?;
                    let eval_on_data = verifier_state.next_extension_scalar()?;
                    retrieved_numerators_value += pref * eval_on_multiplicity;
                    retrieved_denominators_value += pref * eval_on_data;
                    bus_numerators_values.insert(table, eval_on_multiplicity);
                    bus_denominators_values.insert(table, eval_on_data);
                }
                BusMultiplicity::One => {
                    let n_col_entries = bus
                        .data
                        .iter()
                        .filter(|e| e.column().is_some_and(|col| !table_values.contains_key(&col)))
                        .count();
                    let col_evals = verifier_state.next_extension_scalars_vec(n_col_entries)?;
                    let mut eval_iter = col_evals.into_iter();
                    let data_evals: Vec<EF> = bus
                        .data
                        .iter()
                        .map(|entry| match *entry {
                            BusData::Constant(val) => EF::from_usize(val),
                            BusData::Column(col) | BusData::ColumnPlusConstant(col, _) => {
                                let v = if let Some(&cached) = table_values.get(&col) {
                                    cached
                                } else {
                                    let v = eval_iter.next().unwrap();
                                    table_values.insert(col, v);
                                    v
                                };
                                match *entry {
                                    BusData::ColumnPlusConstant(_, ofs) => v + F::from_usize(ofs),
                                    _ => v,
                                }
                            }
                        })
                        .collect();
                    let BusData::Constant(domainsep) = bus.domainsep else {
                        unreachable!("multiplicity-One bus domsep must be a constant");
                    };
                    retrieved_numerators_value += pref * bus.direction.to_field_flag();
                    retrieved_denominators_value +=
                        pref * (c - finger_print(EF::from_usize(domainsep), &data_evals, alphas_eq_poly));
                }
            }
            offset_within_table += 1 << log_n_rows;
        }

        columns_values.insert(table, table_values);
    }

    // Compensates for the final padding `xxx..xxx111...1`
    retrieved_denominators_value += mle_of_zeros_then_ones(final_offset, &point_gkr);
    if retrieved_numerators_value != numerators_value {
        return Err(ProofError::InvalidProof);
    }
    if retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }

    Ok(GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        gkr_point: point_gkr.0,
        columns_values,
        total_gkr_n_vars,
        bytecode_evaluation: Some(Evaluation::new(bytecode_point, bytecode_value)),
    })
}

fn offset_for_table(table: &Table, log_n_rows: usize) -> usize {
    table.bus_interactions().len() << log_n_rows
}

pub fn compute_total_logup_log_size(
    log_memory: usize,
    log_bytecode: usize,
    tables_heights_sorted: &[(Table, VarCount)],
) -> VarCount {
    log2_ceil_usize(compute_total_active_len(
        log_memory,
        log_bytecode,
        tables_heights_sorted,
    ))
}
fn compute_total_active_len(
    log_memory: usize,
    log_bytecode: usize,
    tables_heights_sorted: &[(Table, VarCount)],
) -> usize {
    let max_table_height = 1 << tables_heights_sorted[0].1;
    (1 << log_memory)
        + (1 << log_bytecode).max(max_table_height)
        + tables_heights_sorted
            .iter()
            .map(|(table, log_n_rows)| offset_for_table(table, *log_n_rows))
            .sum::<usize>()
}

#[inline]
fn fill_denoms<Build>(dst: &mut [EFPacking<EF>], build: Build)
where
    Build: Fn(usize) -> EFPacking<EF> + Sync,
{
    dst.par_iter_mut().enumerate().for_each(|(p, slot)| *slot = build(p));
}
