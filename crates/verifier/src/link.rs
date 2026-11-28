//! Hotwire, the verifier's side: one-hot pointer links checked by two chained sum-checks.
//!
//! Every row of an instruction table names its cycle, the memory cells it touches and its instruction by
//! pointers, each committed one-hot in one `K` word. One sum-check runs over the index `j` (the index side), the next
//! over the rows `u`, then the pointer columns `q` (the row side). The index side checks the three links against the scattered
//! pointers: memory and the program by agreement, and the state by one identity over the cycles. Each row scatters
//! its state `ŝ = (1, pc, fp)` and its successor `ŝ'` at its cycle, into `A` and `B`, and
//! `Σ_j eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j) = eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin` says that every cycle below `T` has one
//! row (the constant component), each row's successor is the next cycle's state, and the chain runs from `ŝ_init` to
//! `ŝ_fin`. The row side checks that the scattered arrays are the pointers the rows commit, and that every executed
//! pointer is one-hot. The one-hot check is the mirror test of Emile Wambsgans; one-hot addressing follows Shout
//! (Setty and Thaler). A Keccak operand's later cells are read inside the pointer's window of `2^WINDOW_BITS` cells,
//! its lowest chunk (see [`Functionals`]). The prover's side is `lean_vm_core::link`; the specification is `doc/leanvm`
//! §sec:link.

use crate::field::{E, ONE, ZERO};
use crate::layout::{
    Access, BYTECODE_SLOT_BITS, GLOBAL_COLUMN_BASES, K_BITS, Layout, N_TABLES, OP_DEREF, OPCODE_SLOT, Read, Table, Y,
    gpow,
};
use crate::multilinear::{eq_eval, eq_kernel, index_mle, log2_ceil, padding_weight};
use crate::ring_switch::{RingClaim, RingPiece};
use crate::transcript::{Transcript, grinding_bits, sumcheck};
use crate::{VerifierError, require};

/// The widest pointer one word holds.
pub const MAX_WIDTH: usize = 24;

/// The lowest chunk's bits: a pointer's window, the cells a shifted read reaches.
pub const WINDOW_BITS: usize = 4;

/// How a `width`-bit pointer splits into chunks (§sec:pointers): the lowest `min(WINDOW_BITS, width)` bits, then the
/// fewest chunks whose one-hot blocks fit the rest of 64 bits, widths differing by at most one, the wider first. Chunk
/// `i` covers index bits from `index_shifts[i]` and word bits from `word_shifts[i]`.
#[derive(Clone, Debug)]
pub struct Chunks {
    pub width: usize,
    pub widths: Vec<usize>,
    pub index_shifts: Vec<usize>,
    pub word_shifts: Vec<usize>,
}

impl Chunks {
    pub fn new(width: usize) -> Result<Self, VerifierError> {
        require((1..=MAX_WIDTH).contains(&width), VerifierError::AnnouncedTableSizes)?;
        let low = width.min(WINDOW_BITS);
        let rest = width - low;
        let mut widths = vec![low];
        if rest > 0 {
            widths.extend(
                (1..=rest)
                    .map(|d| (0..d).map(|i| rest / d + usize::from(i < rest % d)).collect::<Vec<_>>())
                    .find(|widths| widths.iter().map(|&w| 1usize << w).sum::<usize>() <= 64 - (1 << low))
                    .expect("one chunk per bit fits"),
            );
        }
        let prefix = |f: &dyn Fn(usize) -> usize| {
            widths
                .iter()
                .scan(0, |at, &w| {
                    let start = *at;
                    *at += f(w);
                    Some(start)
                })
                .collect()
        };
        Ok(Self {
            width,
            index_shifts: prefix(&|w| w),
            word_shifts: prefix(&|w| 1 << w),
            widths,
        })
    }

    pub fn d(&self) -> usize {
        self.widths.len()
    }

    fn part<'a>(&self, point: &'a [E], i: usize) -> &'a [E] {
        &point[self.index_shifts[i]..self.index_shifts[i] + self.widths[i]]
    }
}

/// `T_s(v) = eq(e, v + s)` where `v + s < n`, zero elsewhere: chunk 0 read `s` cells further inside its window, from
/// its eq table `e` over `n` values.
fn window_shift(e: &[E], s: usize) -> Vec<E> {
    (0..e.len()).map(|v| e.get(v + s).copied().unwrap_or(ZERO)).collect()
}

/// The functionals a pointer word is read with, as tables over each chunk's values: `D_i` at the index point `r` and
/// at `1 + r`, then chunk 0's `T_s` per shift `s` from 1 to `max_shift`.
///
/// A one-hot pointer `σ` read `s` cells further is `T_s(e_0)·Π_{i ≥ 1} D_i(e_i) = eq(r, σ + s)·[σ_0 + s < 2^{w_0}]`:
/// a read past its window is zero. An access to such a cell drops out of the scattered sum while its row's
/// coordinates still weigh the presence coefficient, so the memory link fails; a gated-off access takes part in no
/// link.
pub struct Functionals {
    /// `(chunk, table)` per value, in order.
    tables: Vec<(usize, Vec<E>)>,
    d: usize,
    /// `π_{w_i}(r_i) = Π_h r_h·(1 + r_h)` over chunk `i`'s coordinates of `r`.
    pub mirrors: Vec<E>,
}

impl Functionals {
    pub fn new(chunks: &Chunks, r: &[E], max_shift: usize) -> Self {
        let d = chunks.d();
        let eq: Vec<Vec<E>> = (0..d).map(|i| eq_kernel(chunks.part(r, i))).collect();
        let mut tables: Vec<(usize, Vec<E>)> = eq.iter().cloned().enumerate().collect();
        // `eq(1 + r_i, v) = eq(r_i, v')` for `v'` the value `v` with its bits flipped.
        tables.extend(
            eq.iter()
                .enumerate()
                .map(|(i, e)| (i, e.iter().rev().copied().collect())),
        );
        tables.extend((1..=max_shift).map(|s| (0, window_shift(&eq[0], s))));
        let mirrors = (0..d)
            .map(|i| chunks.part(r, i).iter().map(|&x| x * (ONE + x)).fold(ONE, |a, b| a * b))
            .collect();
        Self { tables, d, mirrors }
    }

    /// The values of a word whose 64 bit-slices are `slices`: each functional is linear in the bits.
    pub fn values(&self, chunks: &Chunks, slices: &[E]) -> Vec<E> {
        self.tables
            .iter()
            .map(|(i, table)| {
                E::sum(
                    table
                        .iter()
                        .zip(&slices[chunks.word_shifts[*i]..])
                        .map(|(&e, &s)| e * s),
                )
            })
            .collect()
    }

    /// `(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i(r_i)·D_i(1 + r_i) + π_i)` from a word's values: the
    /// pointer at `r`, the pointer read `s` further, and the mirror certificate. `shifts[s − 1]` is `c_s`.
    pub fn summand(&self, coef: E, shifts: &[E], values: &[E], certs: &[E]) -> E {
        let d = self.d;
        let rest = product(values[1..d].iter().copied());
        let low = coef * values[0] + E::sum(shifts.iter().zip(&values[2 * d..]).map(|(&c, &v)| c * v));
        let cert = E::sum((0..d).map(|i| certs[i] * (values[i] * values[d + i] + self.mirrors[i])));
        low * rest + cert
    }
}

fn product(values: impl IntoIterator<Item = E>) -> E {
    values.into_iter().fold(ONE, |acc, value| acc * value)
}

/// `LT_n(point)`, the multilinear extension of `[j < n]`, for `n ≤ 2^len(point)`.
pub fn less_than(point: &[E], n: u64) -> E {
    ONE + padding_weight(point, n)
}

/// `Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)`, the shift of `eq(ζ, ·)` by one at `r` (lemma lem:shift-eq): a sum over
/// the lowest zero bit `k` of `j`, below which `j` is all ones and `j + 1` all zeros.
pub fn shift_eq(zeta: &[E], r: &[E]) -> E {
    let (mut shift, mut carry) = (ZERO, ONE);
    for (&z, &x) in zeta.iter().zip(r) {
        shift = shift * (ONE + z + x) + carry * (ONE + x) * z;
        carry *= x * (ONE + z);
    }
    shift
}

/// `eq(point, j)` at the integer `j`, LSB-first.
pub fn eq_at(point: &[E], j: u64) -> E {
    point
        .iter()
        .enumerate()
        .fold(ONE, |acc, (h, &x)| acc * if j >> h & 1 == 1 { x } else { ONE + x })
}

/// `Σ_{g < n} Π_h e_h(g_h)` with `e_h(0) = low[h]` and `e_h(1) = high[h]`, for `n ≤ 2^len`: a walk over the
/// binary digits of `n`, from the top.
fn prefix_sum(low: &[E], high: &[E], n: u64) -> E {
    let len = low.len();
    let mut full = Vec::with_capacity(len + 1);
    full.push(ONE);
    for h in 0..len {
        full.push(full[h] * (low[h] + high[h]));
    }
    if n >= 1 << len {
        return full[len];
    }
    let mut total = ZERO;
    let mut prefix = ONE;
    for h in (0..len).rev() {
        if n >> h & 1 == 1 {
            total += prefix * low[h] * full[h];
            prefix *= high[h];
        } else {
            prefix *= low[h];
        }
    }
    total
}

/// `ω_F(χ) = θ_F·Σ_{u < n} eq(τ, u)·eq(χ, u)`, the row weight at the table's row point.
fn omega_at(theta: E, tau: &[E], chi: &[E], n: u64) -> E {
    let low: Vec<E> = tau.iter().zip(chi).map(|(&t, &x)| (ONE + t) * (ONE + x)).collect();
    let high: Vec<E> = tau.iter().zip(chi).map(|(&t, &x)| t * x).collect();
    theta * prefix_sum(&low, &high, n)
}

/// Coefficients of a row round and of a pointer-column round.
fn round_coefficients(d: usize) -> (usize, usize) {
    ((d + 2).max(4) + 1, (d + 1).max(3) + 1)
}

/// What the program side weighs each opcode's slots by, per table `F` and slot `s`: on the rows' weight `ω`
/// (`omega`, and `pc` for a slot read times `pc`), and on `ω·fp` (`frame`).
pub struct SlotWeights {
    pub omega: Vec<[E; 1 << BYTECODE_SLOT_BITS]>,
    pub pc: Vec<[E; 1 << BYTECODE_SLOT_BITS]>,
    pub frame: Vec<[E; 1 << BYTECODE_SLOT_BITS]>,
}

/// The program side's weights (§sec:link-index): the opcode on every row; each operand equation's slots under its
/// first slot's challenge; and each access's reads of its instruction, under `η_mm·μ` and the address or word
/// challenge. `gamma` is `(γ_addr, γ_word)`.
pub fn slot_weights(tables: &[Table], slot: &[E], gamma: [E; 2], mu: &[Vec<E>], eta_mem: E, eta_bc: E) -> SlotWeights {
    let zero = [ZERO; 1 << BYTECODE_SLOT_BITS];
    let mut w = SlotWeights {
        omega: vec![zero; tables.len()],
        pc: vec![zero; tables.len()],
        frame: vec![zero; tables.len()],
    };
    for (t, table) in tables.iter().enumerate() {
        let links = &table.links;
        w.omega[t][OPCODE_SLOT] = eta_bc * slot[OPCODE_SLOT];
        for (slots, _) in &links.bytecode_link().operands {
            for &s in slots {
                w.omega[t][s] += eta_bc * slot[slots[0]];
            }
        }
        for (access, &m) in links.memory.iter().zip(&mu[t]) {
            let m = eta_mem * m;
            if let Some((s, e)) = access.frame {
                w.frame[t][s] += m * gamma[0] * gpow(e);
            }
            for read in &access.reads {
                match *read {
                    Read::Word { .. } => {}
                    Read::Slot { slot, scale } => w.omega[t][slot] += m * gamma[1] * scale,
                    Read::Frame { slot, scale } => w.frame[t][slot] += m * gamma[1] * scale,
                    Read::Pc { slot, scale } => w.pc[t][slot] += m * gamma[1] * scale,
                }
            }
        }
    }
    w
}

/// The `(opcode, slot)` pairs any table reads times `pc`.
pub fn pc_slots(tables: &[Table]) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for table in tables {
        for access in &table.links.memory {
            for read in &access.reads {
                if let Read::Pc { slot, .. } = *read {
                    out.push((table.opcode, slot));
                }
            }
        }
    }
    debug_assert!(out.iter().all(|&(op, _)| op == OP_DEREF));
    out
}

/// A table's row point and its non-pointer columns' values there, as local column and value.
pub type TableValues = (Vec<E>, Vec<(usize, E)>);

/// What the link leaves on the commitment, and where it read the program.
pub struct LinkEnd {
    /// The memory term at `r`, the word table there: the memory's low point, each limb's scale, and the value.
    pub memory: (Vec<E>, [E; 2], E),
    /// Per table, its row point and its non-pointer columns' values there, as local column and value.
    pub columns: Vec<TableValues>,
    /// The pointer columns' 64 bit-slices, one piece per pointer column.
    pub ring: RingClaim,
    /// The index point's program coordinates, `r[..log_bytecode]`, where the link splits the program.
    pub bytecode_point: Vec<E>,
    /// The stream positions of the index side's value at `r` (the memory term) and of the bit-slices.
    pub values_at_r: std::ops::Range<usize>,
    pub bit_slices: std::ops::Range<usize>,
}

/// The pointer width every execution of these sizes takes: the cycle count's bits, the memory's and the program's.
pub fn pointer_width(log_memory: usize, log_bytecode: usize, cycles: u64) -> usize {
    let t = (u64::BITS - cycles.leading_zeros()) as usize;
    t.max(log_memory).max(log_bytecode).max(1)
}

/// The grind before the link's challenges: their error is a degree-`n_rows + 3 + BYTECODE_SLOT_BITS` polynomial in them on the
/// row side (`n_rows` the tallest table's row variables), and the `width + 1` of the index side.
pub fn link_grind_bits(n_rows: usize, width: usize) -> u32 {
    grinding_bits((n_rows + 3 + BYTECODE_SLOT_BITS).max(width + 1) as u128)
}

/// How many challenges the link draws eight to a permutation, after `θ_0`: `θ`'s rest, `γ`, `μ`, `α`, `η` and `ε`,
/// then `τ` over the tallest table's `n_rows` row variables, `ζ` over the pointer width and `ν` over its chunks.
pub fn packed_challenges(tables: &[Table], n_rows: usize, width: usize) -> usize {
    let n_accesses: usize = tables.iter().map(|t| t.links.memory.len()).sum();
    let n_pointers: usize = tables.iter().map(|t| t.links.pointers().len()).sum();
    let d = Chunks::new(width).map_or(0, |c| c.d());
    (N_TABLES - 1) + 5 + n_accesses + BYTECODE_SLOT_BITS + 2 + n_pointers + n_rows + width + d
}

/// Verify the links of the execution `layout` announces, from right after the commitment: the index side, the row side
/// and the terminal check of §sec:link-index to §sec:link-terminal, whose soundness is theorem thm:link.
pub fn verify_link(layout: &Layout, transcript: &mut Transcript) -> Result<LinkEnd, VerifierError> {
    let tables = &layout.tables;
    let heights = &layout.table_log_heights;
    let rows = &layout.table_rows;
    // `T` is the total of the public row counts, which the state identity's soundness rests on: its constant
    // component fixes each cycle's row count only mod 2 (characteristic 2), and an odd count on each of the `T`
    // cycles below `T` from `T` rows in all leaves exactly one row per cycle and none past them.
    let cycles: u64 = rows.iter().sum();
    let chunks = Chunks::new(pointer_width(layout.log_memory, layout.log_bytecode, cycles))?;
    let (width, d) = (chunks.width, chunks.d());
    let pointers: Vec<Vec<usize>> = tables.iter().map(|t| t.links.pointers()).collect();
    let n_pointers: usize = pointers.iter().map(Vec::len).sum();
    let max_shift = tables.iter().map(|t| t.links.max_shift()).max().unwrap_or(0);

    // The challenges, after the grind their error asks for.
    let n_rows = heights.iter().copied().max().unwrap_or(0);
    transcript.grind_check(link_grind_bits(n_rows, width))?;
    // The grind's permutation draws `θ_0`; the rest come eight to a permutation, the ones whose count is fixed
    // first.
    let mut theta = vec![transcript.sample()];
    let mut drawn = transcript
        .samples_packed(packed_challenges(tables, n_rows, width))
        .into_iter();
    let mut take = |n: usize| -> Vec<E> { drawn.by_ref().take(n).collect() };
    theta.extend(take(N_TABLES - 1));
    let gamma_state = take(2);
    // On the address, the word and the presence coordinate; a word `lo + y·hi` takes `γ_word·y` on its high limb.
    let gamma_mem = {
        let g = take(3);
        [g[0], g[1], g[1] * Y, g[2]]
    };
    let mu: Vec<Vec<E>> = tables.iter().map(|t| take(t.links.memory.len())).collect();
    let alpha = take(BYTECODE_SLOT_BITS);
    let [eta_mem, eta_bc]: [E; 2] = take(2).try_into().unwrap();
    // The mirror certificates' coefficients: pointer column `q`'s chunk `c` takes `ε_q·ν_c`.
    let eps = take(n_pointers);
    let tau = take(n_rows);
    let zeta = take(width);
    let nu = take(d);
    debug_assert_eq!(drawn.len(), 0, "packed_challenges counts every draw");
    let slot = eq_kernel(&alpha);
    // `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`: the constant component counts the rows on each cycle.
    let state_gamma = |pc: E, fp: E| ONE + gamma_state[0] * pc + gamma_state[1] * fp;
    let s_init = state_gamma(ONE, ONE);
    let s_fin = state_gamma(gpow((1 << layout.log_bytecode) - 1), ONE);

    // The index side, then the memory term at `r` and the fresh coefficients.
    let claim = eq_at(&zeta, 0) * s_init + eq_at(&zeta, cycles) * s_fin;
    let (r, claim) = sumcheck(transcript, claim, 3, &vec![None; width])?;
    let values_start = transcript.stream_offset();
    let m1 = transcript.next_scalar()?;
    let values_at_r = values_start..transcript.stream_offset();
    let [cert, jump @ ..]: [E; 5] = transcript.samples_packed(5).try_into().unwrap();
    let below = |k: usize| product(r[k.min(width)..].iter().map(|&x| ONE + x));
    let y_mem = gamma_mem[0] * index_mle(&r) + gamma_mem[3] * below(layout.log_memory) + gamma_mem[1] * m1;
    let bytecode_point = r[..layout.log_bytecode].to_vec();
    // The program side's targets at `r`: `X_ω` on the rows' weight, `P_fp` on `ω·fp`. Both weigh an instruction's
    // slots by its opcode.
    let weights = slot_weights(tables, &slot, [gamma_mem[0], gamma_mem[1]], &mu, eta_mem, eta_bc);
    let (mut program, mut frame_program) = (ZERO, ZERO);
    if transcript.checked() {
        let split = layout.bytecode.split(&r[..layout.log_bytecode], &pc_slots(tables))?;
        for t in 0..N_TABLES {
            program += weights.omega[t][OPCODE_SLOT] * gpow(t as u64) * split.count[t];
            for s in OPCODE_SLOT + 1..1 << BYTECODE_SLOT_BITS {
                program += weights.omega[t][s] * split.slots[t][s] + weights.pc[t][s] * split.pc[t][s];
                frame_program += weights.frame[t][s] * split.slots[t][s];
            }
        }
    }
    let below_bc = below(layout.log_bytecode);
    let x_bc = eta_bc * slot[1] * index_mle(&r) + below_bc * (eta_bc * slot[2] + program);
    let p_fp = below_bc * frame_program;
    let eq0_r = below(0);
    // The state identity's weights at `r`: on `A` and on `B`.
    let (eq_zeta_r, shift_zeta_r) = (eq_eval(&zeta, &r), shift_eq(&zeta, &r));

    // The row side.
    let (row_count, column_count) = round_coefficients(d);
    let (chi, claim) = sumcheck(transcript, claim, row_count, &vec![None; n_rows])?;
    let q_vars = log2_ceil(n_pointers as u64);
    let (q_point, claim) = sumcheck(transcript, claim, column_count, &vec![None; q_vars])?;
    let eq_q = eq_kernel(&q_point);

    // The values at the row point, then the pointer words' bit-slices, one message read eight scalars a permutation.
    let n_values: usize = (tables.iter().enumerate())
        .map(|(t, table)| (0..table.width()).filter(|c| !pointers[t].contains(c)).count())
        .sum();
    let values_start = transcript.stream_offset();
    let message = transcript.next_scalars_packed(n_values + K_BITS)?;
    let (mut sent_values, slices) = (message[..n_values].iter().copied(), message[n_values..].to_vec());
    let slices_start = values_start + n_values;
    // What the values make of the summand at the row point.
    let mut columns = Vec::with_capacity(N_TABLES);
    let (mut coef, mut shifts, mut cert_weight, mut base) = (ZERO, vec![ZERO; max_shift], ZERO, ZERO);
    let mut pieces = Vec::with_capacity(n_pointers);
    let mut q = 0;
    for (t, table) in tables.iter().enumerate() {
        let point = chi[..heights[t]].to_vec();
        let corner = product(chi[heights[t]..].iter().map(|&x| ONE + x));
        let mut values = vec![ZERO; table.width()];
        let mut sent = Vec::new();
        for c in (0..table.width()).filter(|c| !pointers[t].contains(c)) {
            values[c] = sent_values.next().expect("a value per column");
            sent.push((c, values[c]));
        }
        let links = &table.links;
        let omega = omega_at(theta[t], &tau[..heights[t]], &point, rows[t]);
        let act = less_than(&point, rows[t]);
        let state = links.state();
        let s_hat = state_gamma(values[state.pc], values[state.fp]);
        let s_next = state_gamma(state.next[0].evaluate(&values), state.next[1].evaluate(&values));

        // The base terms: the payload under ω, and JUMP's identities on every row.
        // An access's committed part: its reads are the pointers' coefficients.
        let access_value = |a: &Access| {
            gamma_mem[0] * a.address.evaluate(&values) + gamma_mem[3] + gamma_mem[1] * a.value.evaluate(&values)
        };
        let bc = links.bytecode_link();
        let r_bc = slot[1] * values[bc.pc]
            + slot[2]
            + slot[OPCODE_SLOT] * gpow(bc.opcode as u64)
            + E::sum(
                bc.operands
                    .iter()
                    .map(|(slots, f)| slot[slots[0]] * f.evaluate(&values)),
            );
        let memory = E::sum(links.memory.iter().zip(&mu[t]).map(|(a, &m)| {
            let gate = a.gate.map_or(ONE, |g| values[g]);
            m * gate * access_value(a)
        }));
        let mut table_base = omega * eq0_r * (eta_mem * memory + eta_bc * r_bc);
        // Only JUMP has constraints (`only_jump_is_constrained`). Its identities take `eq(τ, ·)` and the shared
        // coefficients `jump`, with no per-table `θ_t`: a second constrained table would need its own, or its
        // identities would add to JUMP's.
        if table.n_constraints() > 0 {
            let identities = (table.constraints)(&values);
            let eq_tau = eq_eval(&tau[..heights[t]], &point);
            table_base += eq_tau * E::sum(jump.iter().zip(identities).map(|(&c, i)| c * i));
        }
        base += corner * table_base;

        // The pointer columns' coefficients.
        for (k, &pointer) in pointers[t].iter().enumerate() {
            let e = eq_q[q] * corner;
            match k {
                0 => coef += e * act * (eq_zeta_r * s_hat + shift_zeta_r * s_next),
                1 => coef += e * omega * (x_bc + values[state.fp] * p_fp),
                _ => {
                    // The word reads at this pointer weigh `word(r)`, the memory term.
                    for (access, &m) in links.memory.iter().zip(&mu[t]) {
                        for read in &access.reads {
                            if let Read::Word { pointer: p, scale } = read
                                && *p == pointer
                            {
                                coef += e * omega * eta_mem * m * gamma_mem[1] * m1 * scale.evaluate(&values);
                            }
                        }
                    }
                    for (access, &m) in links.memory.iter().zip(&mu[t]).filter(|(a, _)| a.pointer == pointer) {
                        let gate = access.gate.map_or(ONE, |g| values[g]);
                        let c = e * omega * gate * eta_mem * m * y_mem;
                        match access.shift {
                            0 => coef += c,
                            s => shifts[s - 1] += c,
                        }
                    }
                }
            }
            cert_weight += e * omega * eps[q];
            pieces.push(RingPiece {
                placement: Some(
                    layout.placements[GLOBAL_COLUMN_BASES[t] + pointer].expect("a pointer column is committed"),
                ),
                point: point.clone(),
                scale: eq_q[q],
            });
            q += 1;
        }
        columns.push((point, sent));
    }
    let bit_slices = slices_start..transcript.stream_offset();
    if transcript.checked() {
        let functionals = Functionals::new(&chunks, &r, max_shift);
        let values = functionals.values(&chunks, &slices);
        let eq0_q = product(q_point.iter().map(|&x| ONE + x));
        let certs: Vec<E> = nu.iter().map(|&n| cert * cert_weight * n).collect();
        let last = functionals.summand(coef, &shifts, &values, &certs) + eq0_q * base;
        require(last == claim, VerifierError::LinkTerminal)?;
    }
    let below_mem = below(layout.log_memory);
    Ok(LinkEnd {
        memory: (r[..layout.log_memory].to_vec(), [below_mem, Y * below_mem], m1),
        columns,
        ring: RingClaim { pieces, slices },
        bytecode_point,
        values_at_r,
        bit_slices,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layouts_are_the_window_then_the_fewest_chunks_that_fit() {
        let widths = |w| Chunks::new(w).unwrap().widths;
        assert_eq!(widths(22), vec![4, 3, 3, 3, 3, 3, 3]);
        assert_eq!(widths(21), vec![4, 3, 3, 3, 3, 3, 2]);
        assert_eq!(widths(23), vec![4, 3, 3, 3, 3, 3, 2, 2]);
        assert_eq!(widths(24), vec![4, 3, 3, 3, 3, 2, 2, 2, 2]);
        assert_eq!(widths(16), vec![4; 4]);
        assert_eq!(widths(6), vec![4, 2]);
        assert_eq!(widths(3), vec![3]);
        for w in 1..=MAX_WIDTH {
            let widths = widths(w);
            assert_eq!(widths[0], w.min(WINDOW_BITS));
            assert_eq!(widths.iter().sum::<usize>(), w);
            assert!(widths.iter().map(|&w| 1usize << w).sum::<usize>() <= 64);
        }
    }

    /// `verify_link` weighs constraints by `jump` alone, with no table's `θ_t`: JUMP's four identities, one coefficient
    /// each, and no other table's.
    #[test]
    fn only_jump_is_constrained() {
        let constrained: Vec<(usize, usize)> = (crate::layout::tables().iter())
            .filter(|t| t.n_constraints() > 0)
            .map(|t| (t.opcode, t.n_constraints()))
            .collect();
        assert_eq!(constrained, [(crate::layout::OP_JUMP, 4)]);
    }

    /// `shift_eq` is `Σ_j eq(r, j)·eq(ζ, j + 1)` over `j + 1 < 2^n`, summed out.
    #[test]
    fn shift_eq_is_the_shifted_eq_summed_out() {
        let point = |seed: u64, n: usize| {
            (0..n)
                .map(|h| E::new(seed * 31 + h as u64 * 7 + 3, seed ^ h as u64))
                .collect::<Vec<E>>()
        };
        for n in 0..6 {
            let (zeta, r) = (point(1, n), point(2, n));
            let sum = E::sum((0..(1u64 << n) - 1).map(|j| eq_at(&r, j) * eq_at(&zeta, j + 1)));
            assert_eq!(shift_eq(&zeta, &r), sum, "n = {n}");
        }
    }
}
