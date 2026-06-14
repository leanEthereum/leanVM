use std::collections::BTreeMap;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, Sub};

use backend::*;
use lean_vm::ColIndex;
use tracing::{info_span, instrument};

// Sumcheck to prove validity of AIR constraints
//
// 1] We use back-loaded batching (see https://hackmd.io/s/HyxaupAAA)
//
// 2] We fold variables 'right-to-left' (X_{L-1}, X_{L-2}, ..., X_0), but
// use a custom storage layout to keep SIMD on the early rounds (does not
// impact the verifier):
//
// Let L = number of variables, r = current round index (0 ≤ r < L),
// P = min(ENDIANNESS_PIVOT, L), w = packing_log_width (SIMD lane-index bits),
// and "storage-index bit" = the bit of the storage index that round r's
// fold_at_bit targets.
//
// We bit-reverse the storage of each column within chunks of 2^P elements (once, at init).
// The fold schedule has three phases:
//   - Phase 1, rounds [0, P-w): storage-index bit in [w, P), fully SIMD.
//   - Phase 2, rounds [P-w, P): storage-index bit in [0, w), within SIMD-lane, so
//     we unpack before entering this phase.
//   - Phase 3, rounds [P, L): storage-index bit 0 on unpacked storage
// Edge case: when L = P (tables at the minimum size) phase 1 ends one round
// early, at P-w-1, so `SplitEq` stays in packed mode (its eq_point needs length
// > w; at round P-w-1 the eq_point has length L-(P-w-1)-1 = w).

const ENDIANNESS_PIVOT_AIR: usize = 12;

/// Measurement-driven per-class C2 switch (plan §2/C2 kill rule; measured at
/// T3' on the 1550-sig benchmark, two independent interleaved A/B campaigns:
/// 4 pairs then 3 pairs): poseidon robust (poly -45..-52 ms/run vs fold
/// +2..+5 ms table-update); execution NET REGRESSES (+6.9 ms: poly +1.5,
/// fold +5.4 — its short EF rounds and base-cheap evals do not amortize the
/// table update against the cache transient, plan risk §5.1) -> disabled via
/// `Air::c2_table_profitable` (override in execution/air.rs); ext_op neutral
/// -> enabled. Purely a choice between bit-identical computation strategies.
fn c2_class_enabled<A: Air>(computation: &A) -> bool {
    computation.c2_table_profitable()
}

pub trait OuterSumcheckSession<EF: ExtensionField<PF<EF>>>: Debug {
    fn initial_n_vars(&self) -> usize;
    fn sum(&self) -> EF;
    fn bare_degree(&self) -> usize;
    fn eq_alpha(&self) -> EF;
    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF>;
    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>);
    fn final_column_evals(&self) -> Vec<EF>;
}

/// C2 (h6', Gruen 2024/108 §4 adapted to a non-zerocheck): per-pair table of
/// constraint values `T_i[x] = C(r_0..r_{i-1}, x)` on the session's current
/// folded storage. Lives packed through phase 1 (same layout as the columns),
/// unpacked at the same boundary. The padding tail is NOT materialized: an
/// index at/after the active boundary reads `constraints_eval_at_padding`
/// (padding rows repeat the last row, so folding leaves them fixed).
#[derive(Debug)]
enum C2Store<EF: ExtensionField<PF<EF>>> {
    Packed(Vec<EFPacking<EF>>),
    Unpacked(Vec<EF>),
}

/// Fresh per-pair constraint-eval vectors cached from the current round's
/// pass, used at challenge time to extrapolate `T_{i+1}`. Seed round (local
/// round 0): nodes z = 0, 1, 2, .., d_z. Table rounds: nodes z = 2, .., d_z
/// (z=0 and z=1 come from `T_i[i0]`, `T_i[i1]`).
#[derive(Debug)]
enum C2Cache<EF: ExtensionField<PF<EF>>> {
    Packed(Vec<Vec<EFPacking<EF>>>),
    Unpacked(Vec<Vec<EF>>),
}

#[derive(Debug)]
pub struct AirSumcheckSession<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    eq_factor: Vec<EF>, // The last element is removed at each round
    /// Active element count in the current storage. Always a multiple of
    /// `2^{P - r}` while r < P (chunk-aligned), then ceil-halves afterward.
    current_unpadded_len: usize,
    sum: EF,
    missing_mul_factor: EF,
    computation: A,
    extra_data: A::ExtraData,
    initial_n_vars: usize,
    constraints_eval_at_padding: EF,
    rounds_done: usize,
    /// C2 kill-switch (plan §2/C2): purely a choice between two bit-identical
    /// computation strategies — flipped off permanently on any non-conforming
    /// shape (fallback = the fresh-eval path).
    c2_enabled: bool,
    c2_table: Option<C2Store<EF>>,
    c2_cache: Option<C2Cache<EF>>,
}

impl<'a, EF: ExtensionField<PF<EF>>, A: Air> AirSumcheckSession<'a, EF, A>
where
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF>,
{
    pub fn new(
        packed_multilinears: MleGroup<'a, EF>,
        eq_factor: Vec<EF>,
        sum: EF,
        computation: A,
        extra_data: A::ExtraData,
        non_padded_n_rows: usize,
    ) -> Self {
        let initial_n_vars = packed_multilinears.n_vars();
        assert_eq!(eq_factor.len(), initial_n_vars);
        let last_point = column_evals(&packed_multilinears.by_ref(), (1 << initial_n_vars) - 1);
        let constraints_eval_at_padding = A::eval_extension(&computation, &last_point, &extra_data);

        let pivot = ENDIANNESS_PIVOT_AIR.min(initial_n_vars);
        let has_packed_phase = pivot > packing_log_width::<EF>();

        let padded_n_rows = non_padded_n_rows
            .next_multiple_of(1usize << pivot)
            .min(1usize << initial_n_vars);

        let multilinears = match (packed_multilinears.by_ref(), has_packed_phase) {
            (MleGroupRef::BasePacked(cols), true) => {
                let _span = info_span!("chunk-bit-reversing columns").entered();
                let chunk_size = 1usize << pivot;
                let shift = usize::BITS as usize - pivot;
                let mut bit_reversed: Vec<ArenaVec<PFPacking<EF>>> = vec![ArenaVec::new(); cols.len()];
                parallel::par_chunks_mut(&mut bit_reversed, 1, |i, out_slot| {
                    let src = cols[i];
                    let mut dst: ArenaVec<PFPacking<EF>> = unsafe { ArenaVec::uninitialized(src.len()) };
                    let src_u = PFPacking::<EF>::unpack_slice(src);
                    let dst_u = PFPacking::<EF>::unpack_slice_mut(&mut dst);
                    for (src_chunk, dst_chunk) in src_u.chunks_exact(chunk_size).zip(dst_u.chunks_exact_mut(chunk_size))
                    {
                        for (p, slot) in dst_chunk.iter_mut().enumerate() {
                            *slot = src_chunk[p.reverse_bits() >> shift];
                        }
                    }
                    out_slot[0] = dst;
                });
                MleGroup::Owned(MleGroupOwned::BasePacked(bit_reversed))
            }
            _ => unreachable!(),
        };

        let c2_enabled = c2_class_enabled(&computation);
        Self {
            multilinears,
            eq_factor,
            current_unpadded_len: padded_n_rows,
            sum,
            missing_mul_factor: EF::ONE,
            computation,
            extra_data,
            initial_n_vars,
            constraints_eval_at_padding,
            rounds_done: 0,
            c2_enabled,
            c2_table: None,
            c2_cache: None,
        }
    }

    /// Test-only hook: force the fresh-eval (pre-C2) path so equality tests can
    /// drive both strategies on identical inputs. Both paths are bit-identical
    /// by construction; this switch only selects the slower reference one.
    #[doc(hidden)]
    pub fn set_c2_enabled_for_tests(&mut self, enabled: bool) {
        self.c2_enabled = enabled;
    }
}

impl<'a, EF, A> AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    fn pivot(&self) -> usize {
        ENDIANNESS_PIVOT_AIR.min(self.initial_n_vars)
    }

    // example:  folding_bit = 2
    // storage (RAM): m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7]  m[8] m[9] m[10] m[11]  m[12]…
    //                  ╰────┼────┼────┼────╯    │    │    │    ╰──────┼─────┼─────┼─────╯    │
    //                       ╰────┼────┼─────────╯    │    │           ╰─────┼─────┼──────────╯
    //                            ╰────┼──────────────╯    │                 ╰─────┼───────...
    //                                 ╰───────────────────╯                       ╰───────...
    fn folding_bit(&self) -> usize {
        let pivot = self.pivot();
        if self.rounds_done < pivot {
            pivot - 1 - self.rounds_done
        } else {
            0
        }
    }

    // example:  folding_bit_packed = 2, packing_log_width = 3
    // storage (RAM):  m[0..7] m[8..15] m[16..23] m[24..31] m[32..39] m[40..47] m[48..55] m[56..63]  m[64..71] m[72..79] m[80..87] m[88..95]  m[96]…
    //                  ╰──────────┼─────────┼─────────┼─────────╯        │        │        │            ╰───────────┼──────────┼──────────┼──────────╯
    //                             ╰─────────┼─────────┼──────────────────╯        │        │                        ╰──────────┼──────────┼───────...
    //                                       ╰─────────┼───────────────────────────╯        │                                   ╰──────────┼───────...
    //                                                 ╰────────────────────────────────────╯                                              ╰───────...
    fn folding_bit_packed(&self) -> usize {
        let bit = self.folding_bit();
        if self.in_phase_1() {
            bit - packing_log_width::<EF>()
        } else {
            bit
        }
    }

    fn in_phase_1(&self) -> bool {
        let w = packing_log_width::<EF>();
        // (a) the variable being bound sits above the lane bits, and
        // (b) `SplitEq` can still run in packed mode (`n - r - 1 > w`).
        self.rounds_done + w < self.pivot() && self.rounds_done + w + 1 < self.initial_n_vars
    }

    fn active_count_pairs(&self) -> usize {
        if self.in_phase_1() {
            (self.current_unpadded_len / 2) >> packing_log_width::<EF>()
        } else {
            self.current_unpadded_len.div_ceil(2)
        }
    }

    /// `eq_factor` permuted to match our storage convention: entries in
    /// `[0, n-P)` unchanged, entries in `[n-P, len)` reversed
    fn permuted_alphas(&self, len: usize) -> Vec<EF> {
        let head_len = (self.initial_n_vars - self.pivot()).min(len);
        let base = &self.eq_factor[..len];
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(&base[..head_len]);
        out.extend(base[head_len..].iter().rev().copied());
        out
    }

    /// `C_pad * sum over padded pair positions of partial_eq(new_j)`.
    fn padding_eq_sum(&self, unpadded_len: usize) -> EF {
        let len = self.initial_n_vars - self.rounds_done;
        let mut alphas = self.permuted_alphas(len);
        alphas[len - 1 - self.folding_bit()] = EF::ZERO;
        mle_of_zeros_then_ones(unpadded_len, &alphas)
    }
}

impl<'a, EF, A> OuterSumcheckSession<EF> for AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + Debug + 'static,
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF> + Debug,
{
    fn initial_n_vars(&self) -> usize {
        self.initial_n_vars
    }

    fn sum(&self) -> EF {
        self.sum
    }

    fn bare_degree(&self) -> usize {
        self.computation.degree()
    }

    fn eq_alpha(&self) -> EF {
        *self.eq_factor.last().unwrap()
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        let split_eq = info_span!("split_eq_new")
            .in_scope(|| SplitEq::new(&self.permuted_alphas(self.initial_n_vars - self.rounds_done - 1)));
        let active_count_pairs = self.active_count_pairs();
        let storage_shift = if self.in_phase_1() {
            packing_log_width::<EF>()
        } else {
            0
        };
        let iter_count_pairs = 1usize << (self.initial_n_vars - self.rounds_done - 1 - storage_shift);
        debug_assert!(active_count_pairs <= iter_count_pairs);

        let padding_contribution = if active_count_pairs < iter_count_pairs {
            self.constraints_eval_at_padding * self.padding_eq_sum(self.current_unpadded_len)
        } else {
            EF::ZERO
        };

        // C2 (plan §1.3): seed round caches all node vectors; table rounds get
        // the z=0 accumulator from `T_i` (no constraint eval) and cache only
        // the fresh z = 2..d_z vectors. Any non-conforming shape falls back to
        // the fresh-eval path (bit-identical) and disables C2 for the session.
        let fold_bit = self.folding_bit_packed();
        let is_seed = self.c2_table.is_none();
        #[derive(PartialEq)]
        enum C2RoundMode {
            SeedPacked,
            TablePacked,
            TableUnpacked,
            Fallback,
        }
        let mode = if !self.c2_enabled {
            C2RoundMode::Fallback
        } else {
            match (&self.multilinears.by_ref(), &self.c2_table) {
                (MleGroupRef::BasePacked(_), None) if self.rounds_done == 0 && self.in_phase_1() => {
                    C2RoundMode::SeedPacked
                }
                (MleGroupRef::ExtensionPacked(_), Some(C2Store::Packed(_))) => C2RoundMode::TablePacked,
                (MleGroupRef::Extension(_), Some(C2Store::Unpacked(_))) => C2RoundMode::TableUnpacked,
                _ => C2RoundMode::Fallback,
            }
        };
        if mode == C2RoundMode::Fallback && self.c2_enabled {
            // Non-conforming shape: disable C2 permanently for this session.
            self.c2_enabled = false;
            self.c2_table = None;
        }
        let (p_evals_raw, new_cache): (Vec<EF>, Option<C2Cache<EF>>) = match mode {
            C2RoundMode::SeedPacked => {
                let MleGroupRef::BasePacked(cols) = self.multilinears.by_ref() else {
                    unreachable!()
                };
                // T4': bus-only evals for the on-row nodes (z=0, z=1). The
                // default `eval_bus_only` falls back to the full eval, so this
                // is bit-identical for AIRs without an override.
                let eval_bus_01 = |a: &A, point: &[PFPacking<EF>], xd: &A::ExtraData| -> EFPacking<EF> {
                    let n_cols = a.n_columns();
                    let mut folder = ConstraintFolderPacked::new(&point[..n_cols], &point[n_cols..], xd);
                    a.eval_bus_only(&mut folder, xd);
                    folder.accumulator
                };
                let (accs, cache) = c2_pass::<EF, A, PFPacking<EF>, EFPacking<EF>, _, _, _>(
                    &cols,
                    |j| split_eq.get_packed(j),
                    &self.computation,
                    &self.extra_data,
                    fold_bit,
                    active_count_pairs,
                    A::eval_packed_base,
                    eval_bus_01,
                    None,
                );
                let accs = accs.into_iter().map(unpack_sum_packed::<EF>).collect();
                (accs, Some(C2Cache::Packed(cache)))
            }
            C2RoundMode::TablePacked => {
                let MleGroupRef::ExtensionPacked(cols) = self.multilinears.by_ref() else {
                    unreachable!()
                };
                let Some(C2Store::Packed(table)) = &self.c2_table else {
                    unreachable!()
                };
                let (accs, cache) = c2_pass::<EF, A, EFPacking<EF>, EFPacking<EF>, _, _, _>(
                    &cols,
                    |j| split_eq.get_packed(j),
                    &self.computation,
                    &self.extra_data,
                    fold_bit,
                    active_count_pairs,
                    A::eval_packed_extension,
                    A::eval_packed_extension,
                    Some(table),
                );
                let accs = accs.into_iter().map(unpack_sum_packed::<EF>).collect();
                (accs, Some(C2Cache::Packed(cache)))
            }
            C2RoundMode::TableUnpacked => {
                let MleGroupRef::Extension(cols) = self.multilinears.by_ref() else {
                    unreachable!()
                };
                let Some(C2Store::Unpacked(table)) = &self.c2_table else {
                    unreachable!()
                };
                let (accs, cache) = c2_pass::<EF, A, EF, EF, _, _, _>(
                    &cols,
                    |j| split_eq.get_unpacked(j),
                    &self.computation,
                    &self.extra_data,
                    fold_bit,
                    active_count_pairs,
                    A::eval_extension,
                    A::eval_extension,
                    Some(table),
                );
                (accs, Some(C2Cache::Unpacked(cache)))
            }
            C2RoundMode::Fallback => {
                let fresh = compute_raw_poly(
                    &self.multilinears.by_ref(),
                    &self.computation,
                    &self.extra_data,
                    &split_eq,
                    fold_bit,
                    active_count_pairs,
                );
                (fresh, None)
            }
        };

        // Dual-compute invariant (plan §4 T3' row): in dev builds, the C2 path
        // must reproduce the fresh-eval accumulators exactly.
        #[cfg(debug_assertions)]
        if new_cache.is_some() {
            let fresh = compute_raw_poly(
                &self.multilinears.by_ref(),
                &self.computation,
                &self.extra_data,
                &split_eq,
                fold_bit,
                active_count_pairs,
            );
            debug_assert_eq!(
                p_evals_raw, fresh,
                "C2 dual-compute mismatch (seed={is_seed}, round={})",
                self.rounds_done
            );
        }
        let _ = is_seed;
        self.c2_cache = new_cache;

        let mut p_evals: Vec<EF> = p_evals_raw
            .into_iter()
            .map(|v| (v + padding_contribution) * self.missing_mul_factor)
            .collect();

        let p_at_1 = (self.sum - (EF::ONE - self.eq_alpha()) * p_evals[0]) / self.eq_alpha();
        p_evals.insert(1, p_at_1);

        DensePolynomial::lagrange_interpolation(
            &p_evals
                .iter()
                .enumerate()
                .map(|(i, &val)| (PF::<EF>::from_usize(i), val))
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>) {
        let alpha_fold = self.eq_alpha();
        let eq_eval = (EF::ONE - alpha_fold) * (EF::ONE - challenge) + alpha_fold * challenge;
        self.sum = bare_poly.evaluate(challenge) * eq_eval;
        self.missing_mul_factor *= eq_eval;

        let was_in_phase_1 = self.in_phase_1();
        let fold_bit = self.folding_bit_packed();

        // C2: extrapolate `T_{i+1}[j] = C_pair_j(challenge)` from the cached
        // fresh node vectors (+ `T_i` lookups in table rounds) BEFORE the fold
        // mutates the round geometry. Same pair enumeration as the round pass.
        if self.c2_enabled {
            let new_pairs = self.active_count_pairs();
            let weights = lagrange_weights_at(self.computation.degree_z(), challenge);
            let next = match (self.c2_table.take(), self.c2_cache.take()) {
                (None, Some(C2Cache::Packed(cache))) => Some(C2Store::Packed(c2_update_packed(
                    None, &cache, &weights, fold_bit, new_pairs,
                ))),
                (Some(C2Store::Packed(table)), Some(C2Cache::Packed(cache))) => Some(C2Store::Packed(
                    c2_update_packed(Some(&table), &cache, &weights, fold_bit, new_pairs),
                )),
                (Some(C2Store::Unpacked(table)), Some(C2Cache::Unpacked(cache))) => {
                    Some(C2Store::Unpacked(c2_update_unpacked(
                        &table,
                        &cache,
                        &weights,
                        fold_bit,
                        new_pairs,
                        self.constraints_eval_at_padding,
                    )))
                }
                _ => None,
            };
            match next {
                Some(t) => self.c2_table = Some(t),
                None => {
                    self.c2_enabled = false;
                    self.c2_table = None;
                }
            }
        }

        self.multilinears = self.multilinears.by_ref().fold_at_bit(challenge, fold_bit).into();

        self.current_unpadded_len = self.current_unpadded_len.div_ceil(2);
        self.rounds_done += 1;
        self.eq_factor.pop();

        // Phase 1 → phase 2: unpack (columns and the C2 table together — the
        // table must track the columns' storage mode exactly)
        if was_in_phase_1 && !self.in_phase_1() {
            self.multilinears = self.multilinears.by_ref().unpack().as_owned_or_clone().into();
            if let Some(C2Store::Packed(t)) = &self.c2_table {
                let unpacked: Vec<EF> = EFPacking::<EF>::to_ext_iter(t.iter().copied()).collect();
                self.c2_table = Some(C2Store::Unpacked(unpacked));
            }
        }
    }

    fn final_column_evals(&self) -> Vec<EF> {
        column_evals(&self.multilinears.by_ref(), 0)
    }
}

fn column_evals<EF: ExtensionField<PF<EF>>>(multilinears: &MleGroupRef<'_, EF>, i: usize) -> Vec<EF> {
    match multilinears {
        MleGroupRef::Base(cols) => cols.iter().map(|c| EF::from(c[i])).collect(),
        MleGroupRef::Extension(cols) => cols.iter().map(|c| c[i]).collect(),
        MleGroupRef::BasePacked(cols) => {
            let (packed_i, lane) = (i >> packing_log_width::<EF>(), i & (packing_width::<EF>() - 1));
            cols.iter().map(|c| EF::from(c[packed_i].as_slice()[lane])).collect()
        }
        MleGroupRef::ExtensionPacked(cols) => {
            let (packed_i, lane) = (i >> packing_log_width::<EF>(), i & (packing_width::<EF>() - 1));
            cols.iter()
                .map(|c| EFPacking::<EF>::to_ext_iter([c[packed_i]]).nth(lane).unwrap())
                .collect()
        }
    }
}

fn compute_raw_poly<'a, EF, A>(
    multilinears: &MleGroupRef<'a, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    fold_bit: usize, // in storage
    active_count_pairs: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let unpack_sum_packed = |s: EFPacking<EF>| -> EF { EFPacking::<EF>::to_ext_iter([s]).sum::<EF>() };

    match multilinears {
        MleGroupRef::BasePacked(cols) => compute_raw_poly_impl::<EF, A, PFPacking<EF>, EFPacking<EF>, _, _>(
            cols,
            |j| split_eq.get_packed(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_packed_base,
            unpack_sum_packed,
        ),
        MleGroupRef::ExtensionPacked(cols) => compute_raw_poly_impl::<EF, A, EFPacking<EF>, EFPacking<EF>, _, _>(
            cols,
            |j| split_eq.get_packed(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_packed_extension,
            unpack_sum_packed,
        ),
        MleGroupRef::Base(cols) => compute_raw_poly_impl::<EF, A, PF<EF>, EF, _, _>(
            cols,
            |j| split_eq.get_unpacked(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_base,
            |s| s,
        ),
        MleGroupRef::Extension(cols) => compute_raw_poly_impl::<EF, A, EF, EF, _, _>(
            cols,
            |j| split_eq.get_unpacked(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_extension,
            |s| s,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_raw_poly_impl<EF, A, IF, EFT, GetEq, UnpackSum>(
    cols: &[&[IF]],
    get_split_eq: GetEq,
    computation: &A,
    extra_data: &A::ExtraData,
    fold_bit: usize,
    active_count_pairs: usize,
    eval_fn: impl Fn(&A, &[IF], &A::ExtraData) -> EFT + Sync + Send,
    unpack_sum: UnpackSum,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + Sub<Output = IF> + AddAssign + PrimeCharacteristicRing,
    EFT: Copy + Send + Sync + Add<Output = EFT> + AddAssign + Mul<Output = EFT> + PrimeCharacteristicRing,
    GetEq: Fn(usize) -> EFT + Sync + Send,
    UnpackSum: Fn(EFT) -> EF + Sync + Send,
{
    // Fresh-eval count per pair: sized by the TRUE constraint degree (`degree_z`,
    // see the Air trait doc) — the bare-poly interpolation and the wire format
    // remain sized by the declared degree.
    let degree = computation.degree_z();
    let n_cols = cols.len();
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;

    let acc = parallel::map_reduce_with_state(
        active_count_pairs,
        || (Vec::<IF>::with_capacity(n_cols), Vec::<IF>::with_capacity(n_cols)),
        || vec![EFT::ZERO; degree],
        |(point, diff), acc, new_j| {
            let i_hi = new_j >> fold_bit;
            let i_lo = new_j & lo_mask;
            let i0 = (i_hi << (fold_bit + 1)) | i_lo;
            let i1 = i0 | stride;
            let partial_eq = get_split_eq(new_j);
            point.clear();
            diff.clear();
            for c in cols {
                let lo = c[i0];
                let hi = c[i1];
                point.push(lo);
                diff.push(hi - lo);
            }
            // z = 0 then (skip z = 1) z = 2, 3, …, degree.
            acc[0] += eval_fn(computation, point, extra_data) * partial_eq;
            for k in 0..n_cols {
                point[k] += diff[k];
            }
            for acc_z in &mut acc[1..] {
                for k in 0..n_cols {
                    point[k] += diff[k];
                }
                *acc_z += eval_fn(computation, point, extra_data) * partial_eq;
            }
        },
        |mut a, b| {
            for i in 0..degree {
                a[i] += b[i];
            }
            a
        },
    );

    acc.into_iter().map(unpack_sum).collect()
}

#[inline(always)]
fn unpack_sum_packed<EF: ExtensionField<PF<EF>>>(s: EFPacking<EF>) -> EF {
    EFPacking::<EF>::to_ext_iter([s]).sum::<EF>()
}

/// C2 round pass (plan §1.3). Two modes:
/// - `table = None` (seed, local round 0): fresh evals at z = 0, 1, 2, .., d_z;
///   ALL d_z+1 per-pair vectors cached; message accumulators as today
///   (z=0 weighted into `acc[0]`, z=2.. into `acc[1..]`; z=1 cached only).
/// - `table = Some(T_i)`: `acc[0] = Σ eq·T_i[i0]` (no constraint eval); fresh
///   evals at z = 2..d_z only, cached for the challenge-time extrapolation.
///
/// Returns `(message accumulators, cached node vectors)`. Cached vectors are
/// indexed by `new_j` (same pair enumeration as the accumulators) and written
/// exactly once each via the raw-ptr-in-map_reduce precedent
/// (sc_computation.rs `sumcheck_fold_and_compute_core`).
#[allow(clippy::too_many_arguments)]
fn c2_pass<EF, A, IF, EFT, GetEq, EvalFn, EvalFn01>(
    cols: &[&[IF]],
    get_split_eq: GetEq,
    computation: &A,
    extra_data: &A::ExtraData,
    fold_bit: usize,
    active_count_pairs: usize,
    eval_fn: EvalFn,
    eval_fn_01: EvalFn01,
    table: Option<&[EFT]>,
) -> (Vec<EFT>, Vec<Vec<EFT>>)
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + Sub<Output = IF> + AddAssign + PrimeCharacteristicRing,
    EFT: Copy + Send + Sync + Add<Output = EFT> + AddAssign + Mul<Output = EFT> + PrimeCharacteristicRing,
    GetEq: Fn(usize) -> EFT + Sync + Send,
    EvalFn: Fn(&A, &[IF], &A::ExtraData) -> EFT + Sync + Send,
    EvalFn01: Fn(&A, &[IF], &A::ExtraData) -> EFT + Sync + Send,
{
    let degree = computation.degree_z();
    let n_cols = cols.len();
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;
    let is_seed = table.is_none();
    let n_cached = if is_seed { degree + 1 } else { degree - 1 };

    let cache: Vec<Vec<EFT>> = (0..n_cached)
        .map(|_| unsafe { uninitialized_vec::<EFT>(active_count_pairs) })
        .collect();

    let acc = parallel::map_reduce_with_state(
        active_count_pairs,
        || (Vec::<IF>::with_capacity(n_cols), Vec::<IF>::with_capacity(n_cols)),
        || vec![EFT::ZERO; degree],
        |(point, diff), acc, new_j| {
            let i_hi = new_j >> fold_bit;
            let i_lo = new_j & lo_mask;
            let i0 = (i_hi << (fold_bit + 1)) | i_lo;
            let i1 = i0 | stride;
            let partial_eq = get_split_eq(new_j);
            point.clear();
            diff.clear();
            for c in cols {
                let lo = c[i0];
                let hi = c[i1];
                point.push(lo);
                diff.push(hi - lo);
            }
            // SAFETY: each `new_j` is visited exactly once across all tasks;
            // every cache slot is written exactly once before being read.
            let write_cache = |vec_idx: usize, v: EFT| unsafe {
                let ptr = cache[vec_idx].as_ptr() as *mut EFT;
                *ptr.add(new_j) = v;
            };
            match table {
                None => {
                    // Seed: z = 0 (acc + cache), z = 1 (cache only), z = 2.. (acc + cache).
                    // z=0 / z=1 are evaluations on actual storage rows -> the
                    // bus-only fast path applies (T4'); z = 2.. are off-row
                    // points where genuine gates do NOT vanish -> full eval.
                    let v0 = eval_fn_01(computation, point, extra_data);
                    write_cache(0, v0);
                    acc[0] += v0 * partial_eq;
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    let v1 = eval_fn_01(computation, point, extra_data);
                    write_cache(1, v1);
                    for (zi, acc_z) in acc[1..].iter_mut().enumerate() {
                        for k in 0..n_cols {
                            point[k] += diff[k];
                        }
                        let v = eval_fn(computation, point, extra_data);
                        write_cache(2 + zi, v);
                        *acc_z += v * partial_eq;
                    }
                }
                Some(t) => {
                    // Table: z = 0 from T_i (i0 is always inside the active
                    // prefix — see the padding analysis in the session docs).
                    acc[0] += t[i0] * partial_eq;
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    for (zi, acc_z) in acc[1..].iter_mut().enumerate() {
                        for k in 0..n_cols {
                            point[k] += diff[k];
                        }
                        let v = eval_fn(computation, point, extra_data);
                        write_cache(zi, v);
                        *acc_z += v * partial_eq;
                    }
                }
            }
        },
        |mut a, b| {
            for i in 0..degree {
                a[i] += b[i];
            }
            a
        },
    );

    (acc, cache)
}

/// Lagrange weights `w_k(r)` over the node set `{0, 1, .., d}`:
/// `p(r) = Σ_k w_k(r)·p(k)` for any univariate `p` of degree ≤ d. Exact field
/// arithmetic — the same interpolation the message path performs, evaluated.
fn lagrange_weights_at<EF: Field>(d: usize, r: EF) -> Vec<EF> {
    (0..=d)
        .map(|k| {
            let mut num = EF::ONE;
            let mut den = EF::ONE;
            for m in 0..=d {
                if m != k {
                    num *= r - EF::from_usize(m);
                    den *= EF::from_usize(k) - EF::from_usize(m);
                }
            }
            num * den.inverse()
        })
        .collect()
}

/// `T_{i+1}[new_j] = w_0·T_i[i0] + w_1·T_i[i1] + Σ_z w_z·v_z[new_j]`
/// (packed phase: chunk alignment guarantees `i0`, `i1` stay inside the
/// active prefix — no padding reads; debug-asserted).
fn c2_update_packed<EF: ExtensionField<PF<EF>>>(
    table: Option<&[EFPacking<EF>]>,
    cache: &[Vec<EFPacking<EF>>],
    weights: &[EF],
    fold_bit: usize,
    new_pairs: usize,
) -> Vec<EFPacking<EF>> {
    let w_packed: Vec<EFPacking<EF>> = weights.iter().map(|&w| EFPacking::<EF>::from(w)).collect();
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;
    let mut out = unsafe { uninitialized_vec::<EFPacking<EF>>(new_pairs) };
    const CHUNK_P: usize = 1 << 10;
    parallel::par_chunks_mut(&mut out, CHUNK_P, |chunk_idx, chunk| {
        for (off, slot) in chunk.iter_mut().enumerate() {
            let new_j = chunk_idx * CHUNK_P + off;
            let mut v = match table {
                Some(t) => {
                    let i_hi = new_j >> fold_bit;
                    let i_lo = new_j & lo_mask;
                    let i0 = (i_hi << (fold_bit + 1)) | i_lo;
                    let i1 = i0 | stride;
                    debug_assert!(i1 < t.len(), "packed C2 update read past the active prefix");
                    w_packed[0] * t[i0] + w_packed[1] * t[i1]
                }
                None => w_packed[0] * cache[0][new_j] + w_packed[1] * cache[1][new_j],
            };
            let fresh_off = if table.is_some() { 0 } else { 2 };
            for (zi, w) in w_packed[2..].iter().enumerate() {
                v += *w * cache[fresh_off + zi][new_j];
            }
            *slot = v;
        }
    });
    out
}

/// Unpacked-phase variant; a straddle pair may read `T_i[i1]` at/after the
/// active boundary, which is the (round-invariant) padding constant.
fn c2_update_unpacked<EF: ExtensionField<PF<EF>>>(
    table: &[EF],
    cache: &[Vec<EF>],
    weights: &[EF],
    fold_bit: usize,
    new_pairs: usize,
    pad_value: EF,
) -> Vec<EF> {
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;
    let mut out = unsafe { uninitialized_vec::<EF>(new_pairs) };
    const CHUNK_U: usize = 1 << 12;
    parallel::par_chunks_mut(&mut out, CHUNK_U, |chunk_idx, chunk| {
        for (off, slot) in chunk.iter_mut().enumerate() {
            let new_j = chunk_idx * CHUNK_U + off;
            let i_hi = new_j >> fold_bit;
            let i_lo = new_j & lo_mask;
            let i0 = (i_hi << (fold_bit + 1)) | i_lo;
            let i1 = i0 | stride;
            let t0 = table[i0];
            let t1 = if i1 < table.len() { table[i1] } else { pad_value };
            let mut v = weights[0] * t0 + weights[1] * t1;
            for (zi, w) in weights[2..].iter().enumerate() {
                v += *w * cache[zi][new_j];
            }
            *slot = v;
        }
    });
    out
}

#[instrument(skip_all)]
pub fn prove_batched_air_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    sessions: &mut [Box<dyn OuterSumcheckSession<EF> + 'a>],
) -> MultilinearPoint<EF> {
    let n_rounds = sessions.iter().map(|s| s.initial_n_vars()).max().unwrap_or(0);
    let max_full_degree = sessions.iter().map(|s| s.bare_degree() + 1).max().unwrap_or(1);

    let mut challenges = Vec::with_capacity(n_rounds);
    let mut k: Vec<EF> = vec![EF::ONE; sessions.len()];

    for round in 0..n_rounds {
        let round_span = info_span!("air_round", round).entered();
        let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
        let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                combined_coeffs[1] += k[idx] * session.sum();
            } else {
                let bare_poly = info_span!("air_poly", session = idx).in_scope(|| session.compute_bare_round_poly());
                let full_coeffs = expand_bare_to_full(&bare_poly.coeffs, session.eq_alpha());
                for (i, &c) in full_coeffs.iter().enumerate() {
                    combined_coeffs[i] += k[idx] * c;
                }
                bare_polys[idx] = Some(bare_poly);
            }
        }

        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                k[idx] *= challenge;
            } else if let Some(bare_poly) = &bare_polys[idx] {
                info_span!("air_fold", session = idx).in_scope(|| session.process_challenge(challenge, bare_poly));
            }
        }
        drop(round_span);
    }

    MultilinearPoint(challenges)
}

pub fn compute_shifted_columns<F: Field>(n_shift_columns: usize, columns: &[&[F]]) -> Vec<ArenaVec<F>> {
    // Convention: the first `n_shift_columns` columns are the ones that get shifted.
    let mut out: Vec<ArenaVec<F>> = (0..n_shift_columns).map(|_| ArenaVec::new()).collect();
    parallel::par_chunks_mut(&mut out, 1, |i, slot| {
        let column = columns[i];
        let mut shifted = unsafe { ArenaVec::<F>::uninitialized(column.len()) };
        shifted[..column.len() - 1].copy_from_slice(&column[1..]);
        shifted[column.len() - 1] = column[column.len() - 1];
        slot[0] = shifted;
    });
    out
}

pub fn natural_ordering_point_for_session<EF: Copy>(sumcheck_air_point: &[EF], log_n_rows: usize) -> Vec<EF> {
    sumcheck_air_point[sumcheck_air_point.len() - log_n_rows..]
        .iter()
        .rev()
        .copied()
        .collect()
}

pub fn columns_evals_flat_and_shift<EF: ExtensionField<PF<EF>>, A: Air>(
    air: &A,
    col_evals: &[EF],
    natural_ordering_point: &[EF],
) -> (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>) {
    let n_flat = air.n_columns();
    debug_assert_eq!(col_evals.len(), n_flat + air.n_shift_columns());

    let point = MultilinearPoint(natural_ordering_point.to_vec());

    let evals_eq: BTreeMap<ColIndex, EF> = col_evals[..n_flat].iter().copied().enumerate().collect();
    let evals_next: BTreeMap<ColIndex, EF> = col_evals[n_flat..].iter().copied().enumerate().collect();

    (point, evals_eq, evals_next)
}
