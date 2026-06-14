use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;

mod sparse;
mod trace_gen;
pub use trace_gen::fill_trace_poseidon_8;

use sparse::{PARTIAL_ROUNDS as SPARSE_PARTIAL_ROUNDS, get_partial_constants};

pub(super) const WIDTH: usize = 8;
pub(super) const DIGEST: usize = DIGEST_LEN; // 4
pub const HALF_DIGEST_LEN: usize = DIGEST / 2; // 2

// domainsep encoding: see `tables/mod.rs`.
pub const POSEIDON_DOMAINSEP_BASE: usize = 3;
pub const POSEIDON_FLAG_PERMUTE_SHIFT: usize = 1 << 1;
pub const POSEIDON_FLAG_OUT4_SHIFT: usize = 1 << 2;
pub const POSEIDON_FLAG_LEFT_SHIFT: usize = 1 << 3;
pub const POSEIDON_OFFSET_LEFT_SHIFT: usize = 1 << 4;

// ---------- I/O columns ----------
pub const POSEIDON_8_COL_MULTIPLICITY: ColIndex = 0;
pub const POSEIDON_8_COL_NU_B: ColIndex = 1;
pub const POSEIDON_8_COL_NU_C: ColIndex = 2;
// Output width flags (compression only for out2; out4 also covers permute_half):
//   out2 set  => output is 2 elements (HALF_DIGEST_LEN), compression only.
//   out4 set  => output is 4 elements (DIGEST); for compression a full digest,
//                for permutation the low half (permute_half).
//   neither   => output is 8 elements (WIDTH), full permutation only.
pub const POSEIDON_8_COL_FLAG_OUT2: ColIndex = 3;
pub const POSEIDON_8_COL_FLAG_OUT4: ColIndex = 4;
pub const POSEIDON_8_COL_FLAG_LEFT: ColIndex = 5;
pub const POSEIDON_8_COL_OFFSET_LEFT: ColIndex = 6;
pub const POSEIDON_8_COL_ADDR_LEFT_LO: ColIndex = 7;
pub const POSEIDON_8_COL_ADDR_LEFT_HI: ColIndex = 8;
pub const POSEIDON_8_COL_FLAG_PERMUTE: ColIndex = 9;
pub const POSEIDON_8_COL_INPUT_START: ColIndex = 10;
// Output is the full WIDTH-element permutation state: `out_lo` (WIDTH/2)
// followed by `out_hi` (WIDTH/2). Compression only uses `out_lo`.
pub const POSEIDON_8_COL_OUT_LO: ColIndex = POSEIDON_8_COL_INPUT_START + WIDTH; // 18
pub const POSEIDON_8_COL_OUT_HI: ColIndex = POSEIDON_8_COL_OUT_LO + WIDTH / 2; // 22
pub const POSEIDON_8_COL_ROUND_START: ColIndex = POSEIDON_8_COL_OUT_LO + WIDTH; // 26
/// Non-committed columns ("virtual"):
pub const POSEIDON_8_COL_NU_A: ColIndex = num_cols_poseidon_8();
pub const POSEIDON_8_COL_DOMAINSEP: ColIndex = num_cols_poseidon_8() + 1;

pub const POSEIDON8_NAME: &str = "poseidon8_compress_half";
pub const POSEIDON8_QUARTER_NAME: &str = "poseidon8_compress_quarter";
pub const POSEIDON8_HARDCODED_LEFT_NAME: &str = "poseidon8_compress_half_hardcoded_left";
pub const POSEIDON8_QUARTER_HARDCODED_LEFT_NAME: &str = "poseidon8_compress_quarter_hardcoded_left";
pub const POSEIDON8_PERMUTE_NAME: &str = "poseidon8_permute";
pub const POSEIDON8_PERMUTE_HALF_NAME: &str = "poseidon8_permute_half";
pub const POSEIDON8_PERMUTE_HALF_HARDCODED_LEFT_NAME: &str = "poseidon8_permute_half_hardcoded_left";
pub const ALL_POSEIDON8_NAMES: [&str; 7] = [
    POSEIDON8_NAME,
    POSEIDON8_QUARTER_NAME,
    POSEIDON8_HARDCODED_LEFT_NAME,
    POSEIDON8_QUARTER_HARDCODED_LEFT_NAME,
    POSEIDON8_PERMUTE_NAME,
    POSEIDON8_PERMUTE_HALF_NAME,
    POSEIDON8_PERMUTE_HALF_HARDCODED_LEFT_NAME,
];

// ---------- Per-round aux columns ----------
//
// Goldilocks Poseidon1-8 with the Appendix B sparse partial-round decomposition
// (see `sparse.rs`). The S-box is `x → x⁷` emitted directly as a degree-7
// expression `x·x²·x⁴`, so we commit only the minimum needed to reset degree
// between rounds — no `committed_x3` intermediates.
//
// Per full round: 8 `post[i]` cols (state after MDS).
// Per partial round: 1 `post_sbox` col (the x⁷ output for lane 0); lanes 1..W
// are expressed symbolically as rank-1 updates via `cheap_matmul`.
//
// Constraints:
// - Full round: `post[i] - Σ_j MDS[i][j] · x[j]⁷ = 0`  (deg 7 equality).
// - Partial round: `post_sbox - x⁷ = 0`               (deg 7 equality).
// - Davies-Meyer: `outputs[i] - final_state[i] - inputs[i] = 0`  (deg 1).

const FULL_ROUND_COLS: usize = WIDTH; // 8 post-state
const PARTIAL_ROUND_COLS: usize = 1; // post_sbox

pub const fn is_full_round(r: usize) -> bool {
    r < POSEIDON1_HALF_FULL_ROUNDS || r >= POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS
}

/// First column index of round `r`'s data.
pub const fn round_data_offset(r: usize) -> usize {
    let mut off = POSEIDON_8_COL_ROUND_START;
    let mut i = 0;
    while i < r {
        off += if is_full_round(i) {
            FULL_ROUND_COLS
        } else {
            PARTIAL_ROUND_COLS
        };
        i += 1;
    }
    off
}

pub const fn num_cols_poseidon_8() -> usize {
    round_data_offset(POSEIDON1_N_ROUNDS)
}

pub const fn num_cols_total_poseidon_8() -> usize {
    // +2 for non-committed columns: POSEIDON_8_COL_NU_A, POSEIDON_8_COL_DOMAINSEP
    num_cols_poseidon_8() + 2
}

const AUX_COLS_PER_ROW: usize = num_cols_poseidon_8() - POSEIDON_8_COL_ROUND_START;

// ---------- Witness computation ----------
//
// Replay the Poseidon1-8 permutation on `input`, emitting every committed
// column value in trace order. The partial phase uses the sparse
// decomposition so only 2 cols/round are emitted.

fn mds_vec_mul(state: &[F; WIDTH]) -> [F; WIDTH] {
    // u128-accumulator scheme replicating `mds_mul_scalar`
    // (crates/backend/goldilocks/src/poseidon1.rs:85-110, read-only reference):
    // all MDS8_ROW coefficients are <= 9, so each output is a sum of 8 products
    // bounded by 8 * 9 * (p-1) < 2^71 — accumulate in u128 integers and reduce
    // ONCE per lane via 2^64 = 2^32 - 1 (mod p), instead of 8 fully-reducing
    // field multiplications. hi < 2^7, so hi * (2^32 - 1) fits u64 exactly.
    let s: [u128; WIDTH] = std::array::from_fn(|j| state[j].as_canonical_u64() as u128);
    let mut out = [F::ZERO; WIDTH];
    for i in 0..WIDTH {
        let mut acc: u128 = 0;
        for j in 0..WIDTH {
            acc += MDS8_ROW[(j + WIDTH - i) % WIDTH] as u128 * s[j];
        }
        let lo = acc as u64;
        let hi = (acc >> 64) as u64;
        out[i] = F::from_u64(lo) + F::from_u64(hi * 0xFFFF_FFFF);
    }
    out
}

#[cfg(test)]
fn mds_vec_mul_oracle(state: &[F; WIDTH]) -> [F; WIDTH] {
    let mut out = [F::ZERO; WIDTH];
    for i in 0..WIDTH {
        let mut acc = state[0] * F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
        for j in 1..WIDTH {
            acc += state[j] * F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
        }
        out[i] = acc;
    }
    out
}

fn sbox7(x: F) -> F {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x2 * x
}

/// Returns `(aux, perm_state)`: the per-round witness columns and the raw
/// WIDTH-element permutation output (before any Davies-Meyer feed-forward).
pub fn compute_poseidon8_witness(input: [F; WIDTH]) -> (Vec<F>, [F; WIDTH]) {
    let c = get_partial_constants();
    let mut state = input;
    let mut aux = Vec::with_capacity(AUX_COLS_PER_ROW);

    // Initial full rounds.
    for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
        for (i, s) in state.iter_mut().enumerate() {
            *s = sbox7(*s + rc[i]);
        }
        let post = mds_vec_mul(&state);
        for v in &post {
            aux.push(*v);
        }
        state = post;
    }

    // Partial phase: absorb first_round_constants, apply m_i, then sparse rounds.
    for (i, s) in state.iter_mut().enumerate() {
        *s += c.first_round_constants[i];
    }
    {
        let mut after = [F::ZERO; WIDTH];
        for (i, dst) in after.iter_mut().enumerate() {
            let mut acc = F::ZERO;
            for (j, sj) in state.iter().enumerate() {
                acc += c.m_i[i][j] * *sj;
            }
            *dst = acc;
        }
        state = after;
    }

    for r in 0..SPARSE_PARTIAL_ROUNDS {
        let post_sbox = sbox7(state[0]);
        aux.push(post_sbox);

        state[0] = if r < SPARSE_PARTIAL_ROUNDS - 1 {
            post_sbox + c.round_constants[r]
        } else {
            post_sbox
        };

        // cheap_matmul:
        //   new_state[0] = Σ_j sparse_first_row[r][j] · state[j]
        //   new_state[i] = state[i] + v[r][i-1] · old_state[0]    (for i ≥ 1)
        let old_s0 = state[0];
        let mut new_s0 = F::ZERO;
        for (j, sj) in state.iter().enumerate() {
            new_s0 += c.sparse_first_row[r][j] * *sj;
        }
        state[0] = new_s0;
        for (i, s) in state.iter_mut().enumerate().skip(1) {
            *s += c.v[r][i - 1] * old_s0;
        }
    }

    // Terminal full rounds.
    for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
        let abs = POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS + round;
        for i in 0..WIDTH {
            state[i] = sbox7(state[i] + GOLDILOCKS_POSEIDON1_RC_8[abs][i]);
        }
        let post = mds_vec_mul(&state);
        for v in &post {
            aux.push(*v);
        }
        state = post;
    }

    // `state` now holds the raw permutation output. Compression (Davies-Meyer
    // feed-forward `state[i] + input[i]`) is applied by the caller.
    debug_assert_eq!(aux.len(), AUX_COLS_PER_ROW);
    (aux, state)
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod packed_witness {
    use super::*;
    use backend::{PackedGoldilocksAVX512 as P, mds_mul_simd};

    /// Rows processed per packed call — one row per AVX512 lane.
    pub const WITNESS_LANES: usize = 8;

    #[inline(always)]
    fn sbox7_p(x: P) -> P {
        let x2 = x * x;
        let x4 = x2 * x2;
        x4 * x2 * x
    }

    #[inline(always)]
    fn bcast(c: F) -> P {
        P([c; WITNESS_LANES])
    }

    /// Row-major convenience wrapper over [`compute_poseidon8_witness_packed`]:
    /// transposes 8 scalar input rows into packed lanes first.
    pub fn compute_poseidon8_witness_x8(inputs: &[[F; WIDTH]; WITNESS_LANES]) -> ([P; AUX_COLS_PER_ROW], [P; WIDTH]) {
        let state: [P; WIDTH] = std::array::from_fn(|j| P(std::array::from_fn(|l| inputs[l][j])));
        compute_poseidon8_witness_packed(state)
    }

    /// 8-lane packed variant of [`compute_poseidon8_witness`]: replays 8
    /// independent permutations in lockstep, one row per SIMD lane. Takes and
    /// returns packed column-major data — lane `l` of `aux[k]` equals row
    /// `l`'s scalar `aux[k]` — so a deferred trace fill can load 8 consecutive
    /// rows of each input column and store each `aux[k]` into 8 consecutive
    /// rows of its column with single 64-byte copies. The MDS reuses the
    /// backend's delayed-reduction `mds_mul_simd`; everything else uses the
    /// fully-reducing packed ops, so every emitted value is field-equal to the
    /// scalar path's.
    pub fn compute_poseidon8_witness_packed(mut state: [P; WIDTH]) -> ([P; AUX_COLS_PER_ROW], [P; WIDTH]) {
        let c = get_partial_constants();
        let mut aux = [P::ZERO; AUX_COLS_PER_ROW];
        let mut k = 0;

        // Initial full rounds.
        for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
            for (j, s) in state.iter_mut().enumerate() {
                *s = sbox7_p(*s + bcast(rc[j]));
            }
            state = mds_mul_simd(state);
            aux[k..k + WIDTH].copy_from_slice(&state);
            k += WIDTH;
        }

        // Partial phase: absorb first_round_constants, apply m_i, then sparse rounds.
        for (j, s) in state.iter_mut().enumerate() {
            *s += bcast(c.first_round_constants[j]);
        }
        {
            let mut after = [P::ZERO; WIDTH];
            for (i, dst) in after.iter_mut().enumerate() {
                let mut acc = P::ZERO;
                for (j, sj) in state.iter().enumerate() {
                    acc += *sj * bcast(c.m_i[i][j]);
                }
                *dst = acc;
            }
            state = after;
        }

        for r in 0..SPARSE_PARTIAL_ROUNDS {
            let post_sbox = sbox7_p(state[0]);
            aux[k] = post_sbox;
            k += 1;

            state[0] = if r < SPARSE_PARTIAL_ROUNDS - 1 {
                post_sbox + bcast(c.round_constants[r])
            } else {
                post_sbox
            };

            let old_s0 = state[0];
            let mut new_s0 = P::ZERO;
            for (j, sj) in state.iter().enumerate() {
                new_s0 += *sj * bcast(c.sparse_first_row[r][j]);
            }
            state[0] = new_s0;
            for (i, s) in state.iter_mut().enumerate().skip(1) {
                *s += old_s0 * bcast(c.v[r][i - 1]);
            }
        }

        // Terminal full rounds.
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let abs = POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS + round;
            for (j, s) in state.iter_mut().enumerate() {
                *s = sbox7_p(*s + bcast(GOLDILOCKS_POSEIDON1_RC_8[abs][j]));
            }
            state = mds_mul_simd(state);
            aux[k..k + WIDTH].copy_from_slice(&state);
            k += WIDTH;
        }

        debug_assert_eq!(k, AUX_COLS_PER_ROW);
        (aux, state)
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub use packed_witness::{WITNESS_LANES, compute_poseidon8_witness_packed, compute_poseidon8_witness_x8};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon8Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon8Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon8"
    }

    fn table(&self) -> Table {
        Table::poseidon8()
    }

    fn n_columns_total(&self) -> usize {
        num_cols_total_poseidon_8()
    }

    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(POSEIDON_8_COL_MULTIPLICITY),
            domainsep: BusData::Column(POSEIDON_8_COL_DOMAINSEP),
            data: vec![
                BusData::Column(POSEIDON_8_COL_NU_A),
                BusData::Column(POSEIDON_8_COL_NU_B),
                BusData::Column(POSEIDON_8_COL_NU_C),
            ],
            deferred_claim: false,
        }];
        buses.extend(memory_lookups_consecutive(
            POSEIDON_8_COL_ADDR_LEFT_LO,
            POSEIDON_8_COL_INPUT_START,
            HALF_DIGEST_LEN,
        ));
        buses.extend(memory_lookups_consecutive(
            POSEIDON_8_COL_ADDR_LEFT_HI,
            POSEIDON_8_COL_INPUT_START + HALF_DIGEST_LEN,
            HALF_DIGEST_LEN,
        ));
        buses.extend(memory_lookups_consecutive(
            POSEIDON_8_COL_NU_B,
            POSEIDON_8_COL_INPUT_START + DIGEST,
            DIGEST,
        ));
        buses.extend(memory_lookups_consecutive(
            POSEIDON_8_COL_NU_C,
            POSEIDON_8_COL_OUT_LO,
            DIGEST * 2,
        ));
        buses
    }

    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize, _ending_pc: usize, _mem0: F) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_total_poseidon_8()];
        row[POSEIDON_8_COL_MULTIPLICITY] = F::ZERO;
        row[POSEIDON_8_COL_NU_B] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_NU_C] = F::from_usize(null_hash_ptr);
        // Padding rows are full-digest compression rows (out4).
        row[POSEIDON_8_COL_FLAG_OUT2] = F::ZERO;
        row[POSEIDON_8_COL_FLAG_OUT4] = F::ONE;
        row[POSEIDON_8_COL_FLAG_LEFT] = F::ZERO;
        row[POSEIDON_8_COL_OFFSET_LEFT] = F::ZERO;
        row[POSEIDON_8_COL_ADDR_LEFT_LO] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_ADDR_LEFT_HI] = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        row[POSEIDON_8_COL_FLAG_PERMUTE] = F::ZERO;
        // Inputs stay zero; compute and fill the matching witness + output.
        // Padding rows are compression rows: `out_lo` holds the Davies-Meyer
        // output (= perm_state, since the input is zero), `out_hi` stays zero.
        let (aux, perm_state) = compute_poseidon8_witness([F::ZERO; WIDTH]);
        row[POSEIDON_8_COL_OUT_LO..POSEIDON_8_COL_OUT_LO + WIDTH / 2].copy_from_slice(&perm_state[..WIDTH / 2]);
        for (i, v) in aux.iter().enumerate() {
            row[POSEIDON_8_COL_ROUND_START + i] = *v;
        }
        // Non-committed columns
        row[POSEIDON_8_COL_NU_A] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_DOMAINSEP] = F::from_usize(POSEIDON_DOMAINSEP_BASE + POSEIDON_FLAG_OUT4_SHIFT);
        // Sanity: Davies-Meyer witness must agree with the direct primitive.
        debug_assert_eq!(&perm_state[..DIGEST], &poseidon8_compress([F::ZERO; WIDTH])[..]);
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Poseidon8 {
            half_output,
            hardcoded_offset_left,
            permute,
        } = args
        else {
            unreachable!("Poseidon8 table called with non-Poseidon8 args");
        };
        // out2: half-width compression output (2 elements), compression only.
        // out4: full digest compression output (4 elements) or permute_half (low 4).
        // neither: full 8-element permutation.
        let out2 = half_output && !permute;
        let out4 = (!half_output && !permute) || (half_output && permute);
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
        // Convention:
        //   flag_hardcoded = 0: left input = m[arg_a..arg_a+4] (split as [arg_a..+2], [arg_a+2..+4])
        //   flag_hardcoded = 1: left input = m[offset..offset+2] | m[arg_a..arg_a+2]
        //                   (i.e. arg_a now points to a 2-element data digest, and the first 2
        //                    elements come from the hardcoded prefix at `offset`)
        let left_first_addr = hardcoded_offset_left.unwrap_or(arg_a_usize);
        let left_second_addr = if flag_hardcoded {
            arg_a_usize
        } else {
            arg_a_usize + HALF_DIGEST_LEN
        };
        let mut input = [F::ZERO; WIDTH];
        ctx.memory
            .get_slice_into(left_first_addr, &mut input[..HALF_DIGEST_LEN])?;
        ctx.memory
            .get_slice_into(left_second_addr, &mut input[HALF_DIGEST_LEN..DIGEST])?;
        ctx.memory.get_slice_into(arg_b.to_usize(), &mut input[DIGEST..])?;

        // h12 C-2: the per-round witness columns are deferred to
        // `fill_trace_poseidon_8`'s packed parallel pass — the inline path only
        // needs the permutation output, via the backend's fast scalar permute
        // (field-equal to the sparse witness replay, see sparse.rs equivalence
        // tests).
        let perm_state = poseidon8_permute(input);

        // `output_cols` are the WIDTH output trace columns. For permute rows they
        // hold the raw permutation state; for compression rows `out_lo`
        // holds the Davies-Meyer output (`perm + input`) and `out_hi` is
        // left zero (overwritten from memory by the trace post-pass).
        let res_addr = index_res_a.to_usize();
        let mut output_cols = [F::ZERO; WIDTH];
        if permute {
            output_cols = perm_state;
            // permute_half (half_output) writes the low DIGEST elements only.
            let out_len = if half_output { DIGEST } else { WIDTH };
            ctx.memory.set_slice(res_addr, &perm_state[..out_len])?;
        } else {
            for i in 0..DIGEST {
                output_cols[i] = perm_state[i] + input[i];
            }
            if half_output {
                ctx.memory.set_slice(res_addr, &output_cols[..HALF_DIGEST_LEN])?;
            } else {
                ctx.memory.set_slice(res_addr, &output_cols[..DIGEST])?;
            }
        }

        let hardcoded_offset_left_val = hardcoded_offset_left.unwrap_or(0);

        trace.columns[POSEIDON_8_COL_MULTIPLICITY].push(F::ONE);
        trace.columns[POSEIDON_8_COL_NU_B].push(arg_b);
        trace.columns[POSEIDON_8_COL_NU_C].push(index_res_a);
        trace.columns[POSEIDON_8_COL_FLAG_OUT2].push(F::from_bool(out2));
        trace.columns[POSEIDON_8_COL_FLAG_OUT4].push(F::from_bool(out4));
        trace.columns[POSEIDON_8_COL_FLAG_LEFT].push(F::from_bool(flag_hardcoded));
        trace.columns[POSEIDON_8_COL_OFFSET_LEFT].push(F::from_usize(hardcoded_offset_left_val));
        trace.columns[POSEIDON_8_COL_ADDR_LEFT_LO].push(F::from_usize(left_first_addr));
        trace.columns[POSEIDON_8_COL_ADDR_LEFT_HI].push(F::from_usize(left_second_addr));
        trace.columns[POSEIDON_8_COL_FLAG_PERMUTE].push(F::from_bool(permute));
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_INPUT_START + i].push(*value);
        }
        // Output columns. The AIR constrains `out_lo` (compression rows) or
        // both `out_lo`/`out_hi` (permute rows); columns left
        // unconstrained for a given mode are overwritten from memory by
        // `fill_trace_poseidon_8`'s post-pass so the lookup still matches.
        for (i, value) in output_cols.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_OUT_LO + i].push(*value);
        }
        // The aux columns (POSEIDON_8_COL_ROUND_START..) stay empty here —
        // `fill_trace_poseidon_8` recomputes them from the input columns.
        // Non-committed columns
        trace.columns[POSEIDON_8_COL_NU_A].push(arg_a);
        let domainsep = POSEIDON_DOMAINSEP_BASE
            + POSEIDON_FLAG_PERMUTE_SHIFT * (permute as usize)
            + POSEIDON_FLAG_OUT4_SHIFT * (out4 as usize)
            + POSEIDON_FLAG_LEFT_SHIFT * (flag_hardcoded as usize)
            + POSEIDON_OFFSET_LEFT_SHIFT * hardcoded_offset_left_val;
        trace.columns[POSEIDON_8_COL_DOMAINSEP].push(F::from_usize(domainsep));

        Ok(())
    }
}

/// Constraint count, computed once at monomorphisation. Must match the number
/// of `assert_*` / `declare_values` calls issued in
/// `eval()` exactly; used by the proving pipeline for pre-allocation.
const fn poseidon8_n_constraints(bus: bool) -> usize {
    // 1 boolean flag (active).
    // 4 boolean flags (out2, out4, hardcoded_left, permute).
    // 3 mutex constraints: permute excludes out2; out4 excludes out2; some output mode set.
    // 2 effective_index constraints (linking addr_left_lo/hi to flag_hardcoded).
    // Initial + terminal full rounds: 8 MDS equality gates per round (deg 7).
    // Partial rounds: 1 post_sbox gate per round (deg 7).
    // Output: 2 gates per WIDTH/2 lane (out_lo + out_hi).
    // + 2 bus gates (multiplicity + fingerprint) if enabled.
    let full_gates = 2 * POSEIDON1_HALF_FULL_ROUNDS * WIDTH;
    let partial_gates = POSEIDON1_PARTIAL_ROUNDS;
    let bus_gates = if bus { 2 } else { 0 };
    1 + 4 + 3 + 2 + full_gates + partial_gates + 2 * (WIDTH / 2) + bus_gates
}

impl<const BUS: bool> Air for Poseidon8Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_8()
    }
    fn degree_air(&self) -> usize {
        // S-box is x⁷ → max degree 7. The output gates multiply the linear
        // Davies-Meyer expression by a single linear flag factor, so output
        // gates are at most degree 2; the round gates dominate at degree 7.
        8
    }
    fn degree_z(&self) -> usize {
        // Degree census (h6' plan §1.2; empirically validated: the bare
        // round-poly coefficient at index 8 is [0,0,0] in EVERY round):
        // full-round gates `post − Σ MDS·(state+rc)^7` and partial-round gates
        // `post_sbox − x^7` are degree 7 (state / x are LINEAR in committed
        // columns — the sparse decomposition commits post_sbox precisely to
        // reset degree); all other constraints are degree ≤ 3, bus gates ≤ 2.
        // 0 of 106 constraints reach the declared degree 8, so the z=8 eval
        // pass is provably redundant. `degree_air()` stays 8 (wire format and
        // verifier-side message sizing unchanged).
        7
    }
    fn n_shift_columns(&self) -> usize {
        0
    }
    fn n_constraints(&self) -> usize {
        poseidon8_n_constraints(BUS)
    }
    // h6' T4': bus-only row value for the C2 seed round. Reads the handful of
    // committed columns the bus tuple needs and emits exactly the two bus
    // constraints (alpha indices 0, 1). On witness-consistent rows (including
    // padding copies of the last row) this equals the full `eval` accumulator
    // — pinned per-row by tests/c2_bus_seed.rs and by the proof byte-diff.
    fn eval_bus_only<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        if !BUS {
            self.eval(builder, extra_data);
            return;
        }
        let flat = builder.flat();
        let multiplicity = flat[POSEIDON_8_COL_MULTIPLICITY];
        let nu_b = flat[POSEIDON_8_COL_NU_B];
        let nu_c = flat[POSEIDON_8_COL_NU_C];
        let flag_out4 = flat[POSEIDON_8_COL_FLAG_OUT4];
        let flag_left = flat[POSEIDON_8_COL_FLAG_LEFT];
        let flag_permute = flat[POSEIDON_8_COL_FLAG_PERMUTE];
        let offset_left = flat[POSEIDON_8_COL_OFFSET_LEFT];
        let addr_left_hi = flat[POSEIDON_8_COL_ADDR_LEFT_HI];

        let domainsep_reconstructed = AB::IF::from_usize(POSEIDON_DOMAINSEP_BASE)
            + flag_permute * AB::F::from_usize(POSEIDON_FLAG_PERMUTE_SHIFT)
            + flag_out4 * AB::F::from_usize(POSEIDON_FLAG_OUT4_SHIFT)
            + flag_left * AB::F::from_usize(POSEIDON_FLAG_LEFT_SHIFT)
            + flag_left * offset_left * AB::F::from_usize(POSEIDON_OFFSET_LEFT_SHIFT);
        let one_minus_flag_left = AB::IF::ONE - flag_left;
        let nu_a = addr_left_hi - one_minus_flag_left * AB::F::from_usize(HALF_DIGEST_LEN);

        eval_bus_virtual::<AB, EF>(
            builder,
            extra_data,
            multiplicity,
            domainsep_reconstructed,
            &[nu_a, nu_b, nu_c],
        );
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let c = get_partial_constants();

        // Phase 1 — snapshot every `flat[…]` column read into owned locals so we
        // can then use `builder` mutably without fighting the borrow checker.
        let multiplicity;
        let nu_b;
        let nu_c;
        let flag_out2;
        let flag_out4;
        let flag_left;
        let flag_permute;
        let offset_left;
        let addr_left_lo;
        let addr_left_hi;
        let inputs: [AB::IF; WIDTH];
        let out_lo: [AB::IF; WIDTH / 2];
        let out_hi: [AB::IF; WIDTH / 2];
        // Per full round: `post[0..W]`. Per partial round: `post_sbox`.
        let mut full_posts: Vec<[AB::IF; WIDTH]> = Vec::with_capacity(2 * POSEIDON1_HALF_FULL_ROUNDS);
        let mut partial_post_sboxes: Vec<AB::IF> = Vec::with_capacity(SPARSE_PARTIAL_ROUNDS);
        {
            let flat = builder.flat();
            multiplicity = flat[POSEIDON_8_COL_MULTIPLICITY];
            nu_b = flat[POSEIDON_8_COL_NU_B];
            nu_c = flat[POSEIDON_8_COL_NU_C];
            flag_out2 = flat[POSEIDON_8_COL_FLAG_OUT2];
            flag_out4 = flat[POSEIDON_8_COL_FLAG_OUT4];
            flag_left = flat[POSEIDON_8_COL_FLAG_LEFT];
            flag_permute = flat[POSEIDON_8_COL_FLAG_PERMUTE];
            offset_left = flat[POSEIDON_8_COL_OFFSET_LEFT];
            addr_left_lo = flat[POSEIDON_8_COL_ADDR_LEFT_LO];
            addr_left_hi = flat[POSEIDON_8_COL_ADDR_LEFT_HI];
            inputs = std::array::from_fn(|i| flat[POSEIDON_8_COL_INPUT_START + i]);
            out_lo = std::array::from_fn(|i| flat[POSEIDON_8_COL_OUT_LO + i]);
            out_hi = std::array::from_fn(|i| flat[POSEIDON_8_COL_OUT_HI + i]);

            for round in 0..POSEIDON1_N_ROUNDS {
                let off = round_data_offset(round);
                if is_full_round(round) {
                    let post: [AB::IF; WIDTH] = std::array::from_fn(|i| flat[off + i]);
                    full_posts.push(post);
                } else {
                    partial_post_sboxes.push(flat[off]);
                }
            }
        }

        // Reconstruct domainsep and nu_a (virtual columns) from the committed flags.
        let domainsep_reconstructed = AB::IF::from_usize(POSEIDON_DOMAINSEP_BASE)
            + flag_permute * AB::F::from_usize(POSEIDON_FLAG_PERMUTE_SHIFT)
            + flag_out4 * AB::F::from_usize(POSEIDON_FLAG_OUT4_SHIFT)
            + flag_left * AB::F::from_usize(POSEIDON_FLAG_LEFT_SHIFT)
            + flag_left * offset_left * AB::F::from_usize(POSEIDON_OFFSET_LEFT_SHIFT);

        // addr_left_lo = nu_a * (1 - flag_left) + offset_left * flag_left
        //   ⇒ when flag_left = 0: addr_left_lo = nu_a
        //                         addr_left_hi = nu_a + HALF_DIGEST_LEN
        //   ⇒ when flag_left = 1: addr_left_lo = offset_left
        //                         addr_left_hi = nu_a
        // We define nu_a (virtual) via addr_left_hi:
        //   nu_a = addr_left_hi - (1 - flag_left) * HALF_DIGEST_LEN
        let one_minus_flag_left = AB::IF::ONE - flag_left;
        let nu_a = addr_left_hi - one_minus_flag_left * AB::F::from_usize(HALF_DIGEST_LEN);

        // Phase 2 — bus / declare.
        if BUS {
            eval_bus_virtual::<AB, EF>(
                builder,
                extra_data,
                multiplicity,
                domainsep_reconstructed,
                &[nu_a, nu_b, nu_c],
            );
        } else {
            builder.declare_values(std::slice::from_ref(&multiplicity));
            builder.declare_values(&[nu_a, nu_b, nu_c, domainsep_reconstructed]);
        }

        builder.assert_bool(multiplicity);
        builder.assert_bool(flag_out2);
        builder.assert_bool(flag_out4);
        builder.assert_bool(flag_left);
        builder.assert_bool(flag_permute);
        // permute is mutually exclusive with the half-width compression output.
        builder.assert_zero(flag_permute * flag_out2);
        // out2 / out4 are mutually exclusive.
        builder.assert_zero(flag_out4 * flag_out2);
        // A non-permutation row must specify a compression output width.
        builder.assert_zero((AB::IF::ONE - flag_permute) * (AB::IF::ONE - flag_out4) * (AB::IF::ONE - flag_out2));

        // Constrain addr_left_lo to match its semantics.
        builder.assert_zero(flag_left * (offset_left - addr_left_lo));
        builder.assert_zero(one_minus_flag_left * (nu_a - addr_left_lo));

        // Phase 3 — Poseidon1-8 permutation constraints with Davies-Meyer feed-forward.
        let mut state: [AB::IF; WIDTH] = inputs;

        // ---- Initial full rounds ----
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let sbox_out: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let x = state[i] + AB::F::from_u64(GOLDILOCKS_POSEIDON1_RC_8[round][i].as_canonical_u64());
                // x⁷ = x · (x²)² · x² — 4 Mul nodes in the symbolic DAG.
                let x2 = x * x;
                let x4 = x2 * x2;
                x4 * x2 * x
            });
            let post = full_posts[round];
            for i in 0..WIDTH {
                let mut acc = sbox_out[0] * AB::F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
                for (j, sj) in sbox_out.iter().enumerate().skip(1) {
                    let coeff = AB::F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
                    acc += *sj * coeff;
                }
                builder.assert_zero(post[i] - acc);
            }
            state = post;
        }

        // ---- Partial phase: first_round_constants, m_i, sparse-matmul loop ----
        for (i, s) in state.iter_mut().enumerate() {
            *s += AB::F::from_u64(c.first_round_constants[i].as_canonical_u64());
        }
        {
            let mut after: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let mut acc = state[0] * AB::F::from_u64(c.m_i[i][0].as_canonical_u64());
                for (j, sj) in state.iter().enumerate().skip(1) {
                    acc += *sj * AB::F::from_u64(c.m_i[i][j].as_canonical_u64());
                }
                acc
            });
            std::mem::swap(&mut state, &mut after);
        }

        for (r, post_sbox) in partial_post_sboxes.iter().enumerate().take(SPARSE_PARTIAL_ROUNDS) {
            let x = state[0];
            let post_sbox = *post_sbox;

            // post_sbox = x⁷ (deg 7).
            let x2 = x * x;
            let x4 = x2 * x2;
            builder.assert_zero(post_sbox - x4 * x2 * x);

            // state[0] becomes post_sbox (+ scalar RC, except last round).
            state[0] = if r < SPARSE_PARTIAL_ROUNDS - 1 {
                post_sbox + AB::F::from_u64(c.round_constants[r].as_canonical_u64())
            } else {
                post_sbox
            };

            // cheap_matmul.
            let old_s0 = state[0];
            let mut new_s0 = state[0] * AB::F::from_u64(c.sparse_first_row[r][0].as_canonical_u64());
            for (j, sj) in state.iter().enumerate().skip(1) {
                new_s0 += *sj * AB::F::from_u64(c.sparse_first_row[r][j].as_canonical_u64());
            }
            state[0] = new_s0;
            for (i, s) in state.iter_mut().enumerate().skip(1) {
                *s += old_s0 * AB::F::from_u64(c.v[r][i - 1].as_canonical_u64());
            }
        }

        // ---- Terminal full rounds ----
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let abs = POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS + round;
            let sbox_out: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let x = state[i] + AB::F::from_u64(GOLDILOCKS_POSEIDON1_RC_8[abs][i].as_canonical_u64());
                let x2 = x * x;
                let x4 = x2 * x2;
                x4 * x2 * x
            });
            let post = full_posts[POSEIDON1_HALF_FULL_ROUNDS + round];
            for i in 0..WIDTH {
                let mut acc = sbox_out[0] * AB::F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
                for (j, sj) in sbox_out.iter().enumerate().skip(1) {
                    let coeff = AB::F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
                    acc += *sj * coeff;
                }
                builder.assert_zero(post[i] - acc);
            }
            state = post;
        }

        // Output gates (WIDTH/2 lanes, 2 gates each):
        //   value = state[i] + feedforward * inputs[i]   (feedforward = 1 - permute)
        //  - out_lo[i] = value, always for i < HALF_DIGEST_LEN; for the rest only
        //    when the output is not the half-width compression (gate `1 - out2`).
        //  - out_hi[i] = state[i + WIDTH/2], only on the full permutation
        //    (gate `1 - out4 - out2`).
        // For compression rows feedforward = 1 (Davies-Meyer); for permutation
        // rows feedforward = 0 (raw permutation output).
        let feedforward = AB::IF::ONE - flag_permute;
        let gate_lo_full = AB::IF::ONE - flag_out2;
        let gate_hi = AB::IF::ONE - flag_out4 - flag_out2;
        for i in 0..WIDTH / 2 {
            let value = state[i] + feedforward * inputs[i];
            if i < HALF_DIGEST_LEN {
                builder.assert_zero(value - out_lo[i]);
            } else {
                builder.assert_zero(gate_lo_full * (value - out_lo[i]));
            }
            builder.assert_zero(gate_hi * (state[i + WIDTH / 2] - out_hi[i]));
        }
    }
}

#[cfg(test)]
mod mds_u128_tests {
    use super::*;

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    #[test]
    fn mds_u128_equals_oracle() {
        let mut seed = 0x9E3779B97F4A7C15u64;
        // boundary patterns incl. non-canonical representatives
        let p = 0xFFFF_FFFF_0000_0001u64;
        let specials = [0u64, 1, p - 1, p, p + 1, u64::MAX, 0xFFFF_FFFF, 1 << 63];
        for &v in &specials {
            let st: [F; WIDTH] = std::array::from_fn(|_| F::from_u64(v));
            assert_eq!(mds_vec_mul(&st), mds_vec_mul_oracle(&st), "special {v:#x}");
        }
        for _ in 0..100_000 {
            let st: [F; WIDTH] = std::array::from_fn(|_| F::from_u64(xorshift(&mut seed)));
            let a = mds_vec_mul(&st);
            let b = mds_vec_mul_oracle(&st);
            assert_eq!(a, b);
        }
    }

    #[test]
    #[ignore]
    fn mds_kernel_ab() {
        let mut seed = 7u64;
        let states: Vec<[F; WIDTH]> = (0..200_000)
            .map(|_| std::array::from_fn(|_| F::from_u64(xorshift(&mut seed))))
            .collect();
        let t = std::time::Instant::now();
        let mut sink = F::ZERO;
        for st in &states {
            sink += mds_vec_mul(st)[0];
        }
        let new_dt = t.elapsed();
        let t = std::time::Instant::now();
        for st in &states {
            sink += mds_vec_mul_oracle(st)[0];
        }
        let old_dt = t.elapsed();
        println!(
            "mds new {:?} old {:?} speedup {:.2}x sink={sink:?}",
            new_dt,
            old_dt,
            old_dt.as_secs_f64() / new_dt.as_secs_f64()
        );
    }

    #[test]
    #[ignore]
    fn mds_witness_microbench() {
        let mut seed = 1u64;
        let inputs: Vec<[F; 8]> = (0..10_000)
            .map(|_| std::array::from_fn(|_| F::from_u64(xorshift(&mut seed))))
            .collect();
        let t = std::time::Instant::now();
        let mut sink = F::ZERO;
        for inp in &inputs {
            let (_aux, out) = compute_poseidon8_witness(*inp);
            sink += out[0];
        }
        let dt = t.elapsed();
        println!(
            "compute_poseidon8_witness: {:?} for 10k perms ({:.0} ns/perm), sink={sink:?}",
            dt,
            dt.as_nanos() as f64 / 10_000.0
        );
    }

    /// Deferred-fill equivalence: `fill_trace_poseidon_8` must emit, for every
    /// row, exactly the values the scalar witness replay produces — including
    /// the trailing rows that don't fill a packed block (n chosen odd).
    #[test]
    fn deferred_aux_fill_equals_scalar() {
        let mut seed = 0xDEADBEEF_u64;
        let n = 1003;
        let mut trace: Vec<ArenaVec<F>> = (0..num_cols_total_poseidon_8()).map(|_| ArenaVec::new()).collect();
        for (c, col) in trace.iter_mut().enumerate() {
            if (POSEIDON_8_COL_ROUND_START..POSEIDON_8_COL_ROUND_START + AUX_COLS_PER_ROW).contains(&c) {
                continue; // deferred — left empty, exactly as execute() leaves them
            }
            for _ in 0..n {
                col.push(F::from_u64(xorshift(&mut seed)));
            }
        }
        fill_trace_poseidon_8(&mut trace);

        assert!(trace.iter().all(|col| col.len() == n));
        for i in 0..n {
            let input: [F; WIDTH] = std::array::from_fn(|j| trace[POSEIDON_8_COL_INPUT_START + j][i]);
            let (aux, _) = compute_poseidon8_witness(input);
            for (k, v) in aux.iter().enumerate() {
                assert_eq!(trace[POSEIDON_8_COL_ROUND_START + k][i], *v, "aux[{k}] row {i}");
            }
        }
    }

    /// C-2 PRE-GATE microbench: packed 8-lane witness kernel vs the scalar
    /// post-C-1 path. Bar: >= 2.5x or C-2 is skipped.
    #[test]
    #[ignore]
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    fn packed_witness_microbench() {
        const BATCHES: usize = 16_384; // 131_072 perms per timed rep

        let mut seed = 0xC0FFEE_u64;
        let inputs: Vec<[[F; WIDTH]; WITNESS_LANES]> = (0..BATCHES)
            .map(|_| std::array::from_fn(|_| std::array::from_fn(|_| F::from_u64(xorshift(&mut seed)))))
            .collect();

        // Field-equality of every emitted value vs the scalar reference.
        for batch in inputs.iter().take(64) {
            let (aux_p, out_p) = compute_poseidon8_witness_x8(batch);
            for l in 0..WITNESS_LANES {
                let (aux_s, out_s) = compute_poseidon8_witness(batch[l]);
                for (k, a) in aux_s.iter().enumerate() {
                    assert_eq!(aux_p[k].0[l], *a, "aux[{k}] lane {l}");
                }
                for j in 0..WIDTH {
                    assert_eq!(out_p[j].0[l], out_s[j], "out[{j}] lane {l}");
                }
            }
        }

        // 3 alternating timed reps each; take the min.
        let mut scalar_best = std::time::Duration::MAX;
        let mut packed_best = std::time::Duration::MAX;
        let mut sink = F::ZERO;
        for _ in 0..3 {
            let t = std::time::Instant::now();
            for batch in &inputs {
                for inp in batch {
                    let (aux, out) = compute_poseidon8_witness(*inp);
                    sink += out[0] + aux[AUX_COLS_PER_ROW - 1];
                }
            }
            scalar_best = scalar_best.min(t.elapsed());

            let t = std::time::Instant::now();
            for batch in &inputs {
                let (aux, out) = compute_poseidon8_witness_x8(batch);
                sink += out[0].0[0] + aux[AUX_COLS_PER_ROW - 1].0[WITNESS_LANES - 1];
            }
            packed_best = packed_best.min(t.elapsed());
        }

        let n_perms = (BATCHES * WITNESS_LANES) as f64;
        println!(
            "scalar {:?} ({:.0} ns/perm) | packed {:?} ({:.0} ns/perm) | speedup {:.2}x | sink={sink:?}",
            scalar_best,
            scalar_best.as_nanos() as f64 / n_perms,
            packed_best,
            packed_best.as_nanos() as f64 / n_perms,
            scalar_best.as_secs_f64() / packed_best.as_secs_f64(),
        );
    }
}
