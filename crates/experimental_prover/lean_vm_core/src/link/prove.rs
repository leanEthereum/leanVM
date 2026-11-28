//! Hotwire's prover: the challenges, the index side, the row side and the claims they leave on the commitment.
//!
//! After the commitment the verifier draws the link challenges. The index side runs over `j < 2^W` on arrays the
//! pointers scatter, then the prover sends the memory term `M_1` at its end `r`, and the verifier draws one fresh
//! coefficient per identity. The row side then continues the same claim over every table's rows and
//! the pointer columns. It ends with each table's non-pointer columns at its row point and the 64 bit-slices of the
//! pointer columns, which become point claims and one ring-switched claim.

use super::base::{Base, Block, Weight};
use super::index::{self, Array, Scatter, ShiftEq, Tail, Term};
use super::pointer::Chunks;
use super::row::{self, Coef, RowColumn, RowPoints, RowTable};
use crate::cpu::{KeccakLane, Layout, keccak_value};
use crate::form::{ColumnClaim, Form};
use crate::pcs::{RingSwitchClaim, StackClaim};
use crate::tables::{self, Links, Table};
use ::pcs::stack_open::RingPiece;
use primitives::field::{F64, F128, F128Unreduced, each};
use primitives::multilinear::{eq_table, mle_eval_many_par};
use primitives::transcript::ProverState;
use std::borrow::Cow;
use verifier::layout::{BYTECODE_SLOT_BITS, MEMORY_0, MEMORY_1, OPCODE_SLOT};

/// Entries per task when filling an array over the index.
const TASK: usize = 1 << 12;

/// Indices each worker holds back while it scatters instructions: a loop's instructions recur only once per pass
/// through it, and every worker runs the same hot loops.
const PROGRAM_SLOTS: usize = 4096;

/// A pointer column's words: the column's own in the stack, or a test's changed copy.
enum Words<'a> {
    Stack(&'a [u64]),
    #[cfg(test)]
    Owned(Vec<u64>),
}

impl Words<'_> {
    fn col(&self) -> &[u64] {
        match self {
            Words::Stack(words) => words,
            #[cfg(test)]
            Words::Owned(words) => words,
        }
    }
}

/// The words of a table's pointer column that the index side scatters: the column's own.
#[cfg(not(test))]
fn index_words(_: usize, _: usize, words: &[u64]) -> Words<'_> {
    Words::Stack(words)
}

/// The words of a table's pointer column that the index side scatters: the column's own, unless a test cheats.
#[cfg(test)]
fn index_words(t: usize, column: usize, words: &[u64]) -> Words<'_> {
    match cheat::INDEX_WORD.get() {
        Some((ct, cc, u, word)) if (ct, cc) == (t, column) && u < words.len() => {
            let mut words = words.to_vec();
            words[u] = word;
            Words::Owned(words)
        }
        _ => Words::Stack(words),
    }
}

/// What a table links, and how Hotwire reads its columns.
pub(crate) struct Plan {
    pub links: Links,
    /// The pointer columns, in Hotwire's order ([`Links::pointers`]).
    pub pointers: Vec<usize>,
    /// The columns that gate an access, in order of first use.
    pub gates: Vec<usize>,
    /// Every other column, in local order: what the prover sends at the row point.
    pub values: Vec<usize>,
}

impl Plan {
    pub(crate) fn of(table: &dyn Table) -> Self {
        let links = table.links();
        let pointers = links.pointers().to_vec();
        let mut gates = Vec::new();
        for g in links.memory.iter().filter_map(|a| a.gate) {
            if !gates.contains(&g) {
                gates.push(g);
            }
        }
        let values = (0..table.n_committed_columns())
            .filter(|c| !pointers.contains(c))
            .collect();
        Self {
            links,
            pointers,
            gates,
            values,
        }
    }

    /// The aux index of a gate column on the row side: the state form comes first.
    fn gate_aux(&self, gate: usize) -> usize {
        1 + self.gates.iter().position(|&g| g == gate).expect("a gate")
    }

    /// A pointer column's coefficient on `ω_F` from the access it takes unshifted, and its shift groups, one per
    /// gate, from the accesses it takes shifted; `c` is `η_mm·Y(r)`.
    fn access_coefs(&self, pointer: usize, mu: &[F128], c: F128) -> (Coef, Vec<row::ShiftGroup>) {
        let coef = |gate: Option<usize>| match gate {
            None => Coef::constant(c),
            Some(g) => Coef {
                constant: F128::ZERO,
                aux: Some((self.gate_aux(g), c)),
            },
        };
        let mut omega = None;
        let mut groups: Vec<(Option<usize>, row::ShiftGroup)> = Vec::new();
        for (access, &mu) in self.links.memory.iter().zip(mu) {
            if access.pointer != pointer {
                continue;
            }
            if access.shift == 0 {
                assert!(omega.is_none(), "one unshifted access per pointer");
                let mut base = coef(access.gate);
                base.constant *= mu;
                base.aux = base.aux.map(|(a, s)| (a, s * mu));
                omega = Some(base);
                continue;
            }
            match groups.iter_mut().find(|(g, _)| *g == access.gate) {
                Some((_, group)) => group.weights.push((access.shift, mu)),
                None => groups.push((
                    access.gate,
                    row::ShiftGroup {
                        coef: coef(access.gate),
                        weights: vec![(access.shift, mu)],
                    },
                )),
            }
        }
        (
            omega.unwrap_or(Coef::ZERO),
            groups.into_iter().map(|(_, g)| g).collect(),
        )
    }
}

/// The link challenges, drawn after the commitment.
pub(crate) struct Challenges {
    pub theta: Vec<F128>,
    pub tau: Vec<F128>,
    /// On `pc`, `fp`.
    pub gamma_state: [F128; 2],
    /// On the address, the two limbs (`γ_word` and `γ_word·y`) and the presence coordinate.
    pub gamma_mem: [F128; 4],
    /// Per table, per access.
    pub mu: Vec<Vec<F128>>,
    /// `eq(α_bc, s)` over the sixteen slots of the stacked program.
    pub alpha_bc: Vec<F128>,
    pub zeta: Vec<F128>,
    pub eta_mem: F128,
    pub eta_bc: F128,
    /// Per global pointer column, per chunk: `ε_q·ν_c`.
    pub eps: Vec<Vec<F128>>,
}

impl Challenges {
    /// After the grind their error asks for ([`verifier::link_grind_bits`]). The grind's permutation draws `θ_0`; the
    /// rest come eight to a permutation, the ones whose count is fixed first.
    fn sample(ps: &mut ProverState, plans: &[Plan], taus: &[usize], chunks: &Chunks) -> Self {
        let m = taus.iter().copied().max().unwrap_or(0);
        ps.grind(verifier::link_grind_bits(m, chunks.width));
        let mut theta = vec![ps.sample()];
        let n = verifier::packed_challenges(tables::layout_tables(), m, chunks.width);
        let mut drawn = ps.sample_packed(n).into_iter();
        let mut take = |n: usize| -> Vec<F128> { drawn.by_ref().take(n).collect() };
        theta.extend(take(tables::N_TABLES - 1));
        let gamma_state: [F128; 2] = take(2).try_into().unwrap();
        // A word `lo + y·hi` takes `γ_word·y` on its high limb.
        let [g_addr, g_word, g_pres]: [F128; 3] = take(3).try_into().unwrap();
        let gamma_mem = [g_addr, g_word, g_word * F128::Y, g_pres];
        let mu = plans.iter().map(|p| take(p.links.memory.len())).collect();
        let alpha_bc = take(BYTECODE_SLOT_BITS);
        let [eta_mem, eta_bc]: [F128; 2] = take(2).try_into().unwrap();
        let eps = take(plans.iter().map(|p| p.pointers.len()).sum());
        let tau = take(m);
        let zeta = take(chunks.width);
        let nu = take(chunks.d());
        debug_assert!(drawn.next().is_none(), "the packed draw is used up");
        let eps = eps.iter().map(|&e| nu.iter().map(|&n| e * n).collect()).collect();
        Self {
            theta,
            tau,
            gamma_state,
            gamma_mem,
            mu,
            alpha_bc: eq_table(&alpha_bc),
            zeta,
            eta_mem,
            eta_bc,
            eps,
        }
    }
}

/// A table's payload forms, before the `eq(0, r)` factor: the ungated part `η_mm·Σ μ_p·R_p + η_bc·R^bc`, then one
/// form per gate, `η_mm·Σ μ_p·R_p` over the accesses it gates.
fn payload_forms(table: &dyn Table, plan: &Plan, ch: &Challenges, t: usize) -> (Form, Vec<Form>) {
    let n = table.n_committed_columns();
    let mut ungated = Form::new(n);
    let links = &plan.links;
    let a = &ch.alpha_bc;
    let bc = &links.bytecode;
    ungated.coeffs[bc.pc] += ch.eta_bc * a[1];
    ungated.constant += ch.eta_bc * a[2] + (ch.eta_bc * a[OPCODE_SLOT]).mul_base(primitives::field::g_pow(bc.opcode));
    for (slots, operand) in &bc.operands {
        ungated.add_scaled(operand, ch.eta_bc * a[slots[0]]);
    }
    let mut gated: Vec<Form> = plan.gates.iter().map(|_| Form::new(n)).collect();
    for (access, &mu) in links.memory.iter().zip(&ch.mu[t]) {
        let form = match access.gate {
            None => &mut ungated,
            Some(g) => &mut gated[plan.gate_aux(g) - 1],
        };
        // `γ_0·address + γ_pres + γ_word·value` of the access's committed part: its reads are the pointers'
        // coefficients.
        let w = ch.eta_mem * mu;
        form.add_scaled(&access.address, w * ch.gamma_mem[0]);
        form.constant += w * ch.gamma_mem[3];
        form.add_scaled(&access.value, w * ch.gamma_mem[1]);
    }
    (ungated, gated)
}

/// A table's base blocks, every form scaled by `scale`, and `JUMP`'s identities on every row.
fn blocks(
    table: &dyn Table,
    plan: &Plan,
    ch: &Challenges,
    t: usize,
    scale: F128,
    jump: Option<[F128; 4]>,
) -> Vec<Block> {
    let (ungated, gated) = payload_forms(table, plan, ch, t);
    let mut out = vec![Block {
        weight: Weight::Omega,
        gate: None,
        form: ungated.scaled(scale),
    }];
    out.extend(plan.gates.iter().zip(gated).map(|(&g, form)| Block {
        weight: Weight::Omega,
        gate: Some(g),
        form: form.scaled(scale),
    }));
    if let Some(alphas) = jump.filter(|_| table.n_constraints() > 0) {
        out.push(Block {
            weight: Weight::Eq,
            gate: None,
            form: table.constraint(&alphas),
        });
    }
    out
}

/// One past the last row that differs from the padrow in any column, at least `rows`, even, at most `2^log_rows`.
fn explicit_rows(columns: &[&[F64]], padrow: &[F64], rows: usize, log_rows: usize) -> usize {
    let last = parallel::map_collect(columns.len(), |c| {
        columns[c].iter().rposition(|&v| v != padrow[c]).map_or(0, |u| u + 1)
    });
    let e = last.into_iter().max().unwrap_or(0).max(rows);
    (e + (e & 1)).min(1 << log_rows)
}

/// `f(j, g^j)` for `j < n`, in parallel: each task seeds `g^j` once and steps it by `g`.
fn tabulate_powers(n: usize, f: impl Fn(usize, F64) -> F128 + Sync) -> Vec<F128> {
    tabulate_powers_in(n, |_| (), |(), j, g_j| f(j, g_j))
}

/// [`tabulate_powers`] with `window` made once per task from its entries' range, for `f` to read from.
fn tabulate_powers_in<W>(
    n: usize,
    window: impl Fn(std::ops::Range<usize>) -> W + Sync,
    f: impl Fn(&W, usize, F64) -> F128 + Sync,
) -> Vec<F128> {
    // SAFETY: every entry is written.
    unsafe {
        primitives::filled_vec(n, |out| {
            parallel::chunks_mut(out, TASK, |task, chunk| {
                let mut g = primitives::field::g_pow(task * TASK);
                let start = task * TASK;
                let w = window(start..start + chunk.len());
                for (k, o) in chunk.iter_mut().enumerate() {
                    o.write(f(&w, start + k, g));
                    g = primitives::field::mul_by_g(g);
                }
            })
        })
    }
}

/// `f(j)` for `j < n`, in parallel.
fn tabulate(n: usize, f: impl Fn(usize) -> F128 + Sync) -> Vec<F128> {
    // SAFETY: every entry is written.
    unsafe {
        primitives::filled_vec(n, |out| {
            parallel::chunks_mut(out, TASK, |task, chunk| {
                for (k, o) in chunk.iter_mut().enumerate() {
                    o.write(f(task * TASK + k));
                }
            })
        })
    }
}

/// `Π_{h ≥ k} (1 + x_h)`: the multilinear extension of `[j < 2^k]`.
fn below_power(point: &[F128], k: usize) -> F128 {
    point[k.min(point.len())..].iter().map(|&x| F128::ONE + x).product()
}

/// What the program side weighs each opcode's slots by, per table and slot (`verifier::link::SlotWeights`): on the
/// rows' weight `ω` (`omega`, and `pc` for a slot read times `pc`), and on `ω·fp` (`frame`).
struct SlotWeights {
    omega: Vec<[F128; 1 << BYTECODE_SLOT_BITS]>,
    pc: Vec<[F128; 1 << BYTECODE_SLOT_BITS]>,
    frame: Vec<[F128; 1 << BYTECODE_SLOT_BITS]>,
}

impl SlotWeights {
    fn new(plans: &[Plan], ch: &Challenges) -> Self {
        let n = plans.len();
        let mut w = Self {
            omega: vec![[F128::ZERO; 1 << BYTECODE_SLOT_BITS]; n],
            pc: vec![[F128::ZERO; 1 << BYTECODE_SLOT_BITS]; n],
            frame: vec![[F128::ZERO; 1 << BYTECODE_SLOT_BITS]; n],
        };
        let (a, gm) = (&ch.alpha_bc, &ch.gamma_mem);
        for (t, plan) in plans.iter().enumerate() {
            w.omega[t][OPCODE_SLOT] = ch.eta_bc * a[OPCODE_SLOT];
            for (slots, _) in &plan.links.bytecode.operands {
                for &s in slots {
                    w.omega[t][s] += ch.eta_bc * a[slots[0]];
                }
            }
            for (access, &mu) in plan.links.memory.iter().zip(&ch.mu[t]) {
                let m = ch.eta_mem * mu;
                if let Some((s, e)) = access.frame {
                    w.frame[t][s] += (m * gm[0]).mul_base(primitives::field::g_pow(e as usize));
                }
                for read in &access.reads {
                    match *read {
                        tables::Read::Word { .. } => {}
                        tables::Read::Slot { slot, scale } => w.omega[t][slot] += m * gm[1] * scale,
                        tables::Read::Frame { slot, scale } => w.frame[t][slot] += m * gm[1] * scale,
                        tables::Read::Pc { slot, scale } => w.pc[t][slot] += m * gm[1] * scale,
                    }
                }
            }
        }
        w
    }
}

/// `constant + Σ coef·col` over a table's columns.
struct Affine {
    constant: F128,
    cols: Vec<(usize, F128)>,
}

impl Affine {
    /// A form without products, its columns of nonzero coefficient.
    fn of(form: &Form) -> Self {
        assert!(form.prods.is_empty(), "an affine form");
        let cols = (form.coeffs.iter().enumerate())
            .filter(|(_, c)| !c.is_zero())
            .map(|(i, &c)| (i, c))
            .collect();
        Self {
            constant: form.constant,
            cols,
        }
    }

    /// The value on a row whose column `c` is `col(c)`.
    #[inline(always)]
    fn at(&self, col: impl Fn(usize) -> F64) -> F128 {
        (self.cols.iter()).fold(self.constant, |acc, &(c, coef)| acc + coef.mul_base(col(c)))
    }

    /// The values on `rows` of the columns `cols`, into `out`.
    #[inline(always)]
    fn rows(&self, cols: &[&[F64]], rows: std::ops::Range<usize>, out: &mut [F128]) {
        let terms = self.cols.iter().map(|&(c, coef)| (coef, &cols[c][rows.clone()]));
        each::affine_each(out, self.constant, terms);
    }
}

/// A table's reads of the word at one pointer: `read·word(σ)` summed over its accesses under `μ`.
struct WordReads {
    pointer: usize,
    read: Affine,
}

/// Each pointer a table of `n_cols` columns reads words at, with what it reads there under `scale·μ`.
fn word_reads(plan: &Plan, n_cols: usize, mu: &[F128], scale: F128) -> Vec<WordReads> {
    let mut out: Vec<(usize, Form)> = Vec::new();
    for (access, &mu) in plan.links.memory.iter().zip(mu) {
        for read in &access.reads {
            let tables::Read::Word { pointer, scale: read } = read else {
                continue;
            };
            let at = match out.iter().position(|(p, _)| p == pointer) {
                Some(at) => at,
                None => {
                    out.push((*pointer, Form::new(n_cols)));
                    out.len() - 1
                }
            };
            out[at].1.add_scaled(read, scale * mu);
        }
    }
    (out.into_iter())
        .map(|(pointer, read)| WordReads {
            pointer,
            read: Affine::of(&read),
        })
        .collect()
}

/// What the link leaves: the memory claim and the table columns' claims at their row points, the pointer columns'
/// ring-switched claim, and the Keccak reduction's claim on the permutation's output.
pub(crate) struct LinkEnd {
    pub memory: StackClaim,
    pub columns: Vec<ColumnClaim>,
    pub ring: RingSwitchClaim,
    pub output: keccak_gkr::OutputClaim,
}

/// Prove the links of an execution whose committed columns are `columns` (every global column, virtual ones
/// included), of `layout`, running `program`.
pub(crate) fn prove(ps: &mut ProverState, layout: &Layout, columns: &[&[F64]], program: &[u64]) -> LinkEnd {
    let chunks = Chunks::new(layout.pointer_width);
    let width = chunks.width;
    let n = 1usize << width;
    let all = tables::tables();
    let plans: Vec<Plan> = all.iter().map(|&t| Plan::of(t)).collect();
    let taus = layout.taus;
    let rows = layout.rows;
    let local = |t: usize| {
        &columns[tables::GLOBAL_COLUMN_BASES[t]..tables::GLOBAL_COLUMN_BASES[t] + all[t].n_committed_columns()]
    };
    let ch = Challenges::sample(ps, &plans, &taus, &chunks);
    let weights = SlotWeights::new(&plans, &ch);
    let cycles: usize = rows.iter().sum();
    let log_mem = layout.placements[MEMORY_0].n_vars;
    // The program's columns, the opcode then the operand slots, from the stacked bytecode, whose slot
    // `OPCODE_SLOT + s` holds column `s`.
    let bytecode_size = program.len() >> BYTECODE_SLOT_BITS;
    let program: Vec<&[F64]> = (program.chunks_exact(bytecode_size).skip(OPCODE_SLOT))
        .map(primitives::cast_slice)
        .collect();

    // ω_F on each table's executed rows, and the state form `s_γ` on its explicit rows.
    let mut omegas: Vec<Vec<F128>> = (0..tables::N_TABLES)
        .map(|t| {
            // SAFETY: the fill writes every entry.
            let mut e = unsafe {
                primitives::filled_vec(1 << taus[t], |out| {
                    primitives::multilinear::fill_eq_table(&ch.tau[..taus[t]], ch.theta[t], out)
                })
            };
            e.truncate(rows[t]);
            e
        })
        .collect();
    let padrows: Vec<Vec<F64>> = all.iter().map(|t| t.padding()).collect();
    let explicit: Vec<usize> = (0..tables::N_TABLES)
        .map(|t| explicit_rows(local(t), &padrows[t], rows[t], taus[t]))
        .collect();
    // Each table's state `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp` and successor `ŝ'_γ`, affine in its columns.
    let state_forms: Vec<[Affine; 2]> = (0..tables::N_TABLES)
        .map(|t| {
            let s = &plans[t].links.state;
            let mut state = Form::new(all[t].n_committed_columns());
            state.constant = F128::ONE;
            let mut next = state.clone();
            state.coeffs[s.pc] += ch.gamma_state[0];
            state.coeffs[s.fp] += ch.gamma_state[1];
            next.add_scaled(&s.next[0], ch.gamma_state[0]);
            next.add_scaled(&s.next[1], ch.gamma_state[1]);
            [Affine::of(&state), Affine::of(&next)]
        })
        .collect();
    let states_at = |t: usize, u: usize| {
        let cols = local(t);
        state_forms[t].each_ref().map(|form| form.at(|c| cols[c][u]))
    };

    // The base terms' `ω` blocks' first row round, which also gives the index side its payload.
    let mut base_firsts = Vec::new();
    // Each pointer column's indices, in `Plan::pointers` order, decoded once for both sides.
    let pointer_words: Vec<&[u64]> = (0..tables::N_TABLES)
        .flat_map(|t| {
            plans[t]
                .pointers
                .iter()
                .map(move |&c| primitives::cast_slice(local(t)[c]))
        })
        .collect();
    let mut decoded = chunks.decode_many(&pointer_words).into_iter();
    let mut indices: Vec<Vec<Vec<u32>>> = (0..tables::N_TABLES)
        .map(|t| decoded.by_ref().take(plans[t].pointers.len()).collect())
        .collect();
    let index_end = tracing::info_span!("Index side").in_scope(|| {
        let scatter = tracing::info_span!("Scatter").entered();
        let pointer = |t: usize, c: usize| {
            let (plan, cols, n_t) = (&plans[t], local(t), rows[t]);
            let k = plan.pointers.iter().position(|&p| p == c).expect("a pointer column");
            match index_words(t, c, &primitives::cast_slice(cols[c])[..n_t]) {
                Words::Stack(w) => (Words::Stack(w), Cow::Borrowed(&indices[t][k][..n_t])),
                #[cfg(test)]
                Words::Owned(w) => {
                    let index = chunks.decode_all(&w);
                    (Words::Owned(w), Cow::Owned(index))
                }
            }
        };
        let cycles_at: Vec<_> = (0..tables::N_TABLES)
            .map(|t| pointer(t, plans[t].links.state.cycle))
            .collect();
        let fill = |lens: [usize; 6]| {
            let arrays = lens.map(Scatter::new);
            let [states, nexts, w_mem, w_bc, v_word, w_fp] = &arrays;
            // Every table's cycles in one pass over the cycle-indexed arrays: `A` and `B`, each row's state and
            // successor at its cycle.
            let cycle_words: Vec<(&[u64], &[u32])> = cycles_at.iter().map(|(w, at)| (w.col(), &at[..])).collect();
            Scatter::add_sorted_words_to(&chunks, &cycle_words, [(states, 0), (nexts, 0)], |t, rows, out| {
                for (form, out) in state_forms[t].iter().zip(out) {
                    form.rows(local(t), rows.clone(), out);
                }
            });
            for t in 0..tables::N_TABLES {
                let (plan, cols, omega) = (&plans[t], local(t), &omegas[t]);
                let pointer = |c: usize| pointer(t, c);
                // Every access of the table in one pass over its rows.
                let memory = &plan.links.memory;
                let pointers: Vec<_> = memory.iter().map(|access| pointer(access.pointer)).collect();
                let accesses: Vec<(&[u64], &[u32], usize)> = (pointers.iter().zip(memory))
                    .map(|((words, at), access)| (words.col(), &at[..], access.shift))
                    .collect();
                w_mem.add_local_accesses(&chunks, &accesses, |a, rows, out| {
                    each::scale_each(out, ch.mu[t][a], &omega[rows.clone()]);
                    if let Some(g) = memory[a].gate {
                        each::mul_base_each(out, &cols[g][rows]);
                    }
                });
                // The word reads: `γ_word·μ·scale(u)` at the pointer each reads, under `ω`.
                let reads = word_reads(plan, all[t].n_committed_columns(), &ch.mu[t], ch.gamma_mem[1]);
                if !reads.is_empty() {
                    let at: Vec<_> = reads.iter().map(|w| pointer(w.pointer)).collect();
                    let entries: Vec<(&[u64], &[u32], usize)> =
                        at.iter().map(|(words, at)| (words.col(), &at[..], 0)).collect();
                    v_word.add_local_accesses(&chunks, &entries, |a, rows, out| {
                        reads[a].read.rows(cols, rows.clone(), out);
                        each::mul_each(out, &omega[rows]);
                    });
                }
                let (bc, at) = pointer(plan.links.bytecode.pointer);
                w_bc.add_repeated_words::<PROGRAM_SLOTS>(&chunks, bc.col(), &at, 0, |rows, out| {
                    out.copy_from_slice(&omega[rows])
                });
                let fp = cols[plan.links.state.fp];
                w_fp.add_repeated_words::<PROGRAM_SLOTS>(&chunks, bc.col(), &at, 0, |rows, out| {
                    out.copy_from_slice(&omega[rows.clone()]);
                    each::mul_base_each(out, &fp[rows]);
                });
            }
            arrays
        };
        // Sized for an honest execution's indices: cycles, memory cells and bytecode entries. An index past these
        // makes the arrays again at the full `2^W`.
        let lens = [cycles, cycles, 1 << log_mem, bytecode_size, 1 << log_mem, bytecode_size];
        let mut arrays = fill(lens.map(|l| l.min(n)));
        if arrays.iter().any(Scatter::overflowed) {
            arrays = fill([n; 6]);
        }

        drop(scatter);
        let _tables = tracing::info_span!("Index tables").entered();
        // The memory and program tables are `g^j` terms past their cells and instructions: each is stored only as
        // far as the array it multiplies reaches, rounded to a power of two. `eq(ζ, ·)` and its shift are not stored
        // at all.
        let [states, nexts, w_mem, w_bc, v_word, w_fp] = arrays.map(Scatter::into_vec);
        let reach = |own: usize, partner: usize| own.max(partner).max(1).next_power_of_two().min(n);
        let (mem_len, bc_len) = (reach(1 << log_mem, w_mem.len()), reach(bytecode_size, w_bc.len()));
        let gm = ch.gamma_mem;
        let mem = &columns[MEMORY_0..=MEMORY_1];
        // The word table, `lo + y·hi` per cell: the two memory columns' limbs as they are.
        let words = {
            let (m0, m1) = (&mem[0][..1 << log_mem], &mem[1][..1 << log_mem]);
            tabulate(1 << log_mem, |j| F128::new(m0[j].0, m1[j].0))
        };
        // Each task reads its memory cells as one run of each column.
        let cells = |r: std::ops::Range<usize>| {
            let (start, end) = (r.start.min(1 << log_mem), r.end.min(1 << log_mem));
            (start, &mem[0][start..end], &mem[1][start..end])
        };
        // Each entry's mixed products are summed unreduced and reduced once.
        let y_mem = tabulate_powers_in(mem_len, cells, |(start, m0, m1), j, g_j| {
            let y = gm[0].mul_base_unreduced(g_j);
            if j < 1 << log_mem {
                let cell = gm[1].mul_base_unreduced(m0[j - start]) ^ gm[2].mul_base_unreduced(m1[j - start]);
                (y ^ cell).reduce() + gm[3]
            } else {
                y.reduce()
            }
        });
        // The program side's targets: `X_ω` under the rows' weight and `P_fp` under `ω·fp`, each weighing an
        // instruction's slots by its opcode.
        let a = &ch.alpha_bc;
        let (x_g, x_one) = (ch.eta_bc * a[1], ch.eta_bc * a[2]);
        let reads_pc: Vec<bool> = (weights.pc.iter()).map(|w| w.iter().any(|c| !c.is_zero())).collect();
        let x_bc = tabulate_powers(bc_len, |j, g_j| {
            let mut x = x_g.mul_base_unreduced(g_j);
            if j < bytecode_size {
                let op = program[0][j].0.trailing_zeros() as usize;
                let w = &weights.omega[op];
                for (s, column) in program.iter().enumerate() {
                    x ^= w[OPCODE_SLOT + s].mul_base_unreduced(column[j]);
                }
                let mut x = x.reduce() + x_one;
                if reads_pc[op] {
                    let p = &weights.pc[op];
                    for (s, column) in program.iter().enumerate().skip(1) {
                        x += p[OPCODE_SLOT + s].mul_base(g_j * column[j]);
                    }
                }
                return x;
            }
            x.reduce()
        });
        let p_fp = tabulate(bytecode_size, |j| {
            let op = program[0][j].0.trailing_zeros() as usize;
            let w = &weights.frame[op];
            let mut x = F128Unreduced::ZERO;
            for (s, column) in program.iter().enumerate().skip(1) {
                x ^= w[OPCODE_SLOT + s].mul_base_unreduced(column[j]);
            }
            x.reduce()
        });
        let firsts: Vec<[F128; 5]> = (0..tables::N_TABLES)
            .map(|t| {
                let base = Base::new(
                    blocks(all[t], &plans[t], &ch, t, F128::ONE, None),
                    local(t).to_vec(),
                    &padrows[t],
                    None,
                );
                base.omega_round(&omegas[t], ch.tau.first().copied())
            })
            .collect();
        let payload: F128 = firsts.iter().flat_map(|f| f[1..].iter().copied()).sum();
        drop(_tables);
        base_firsts = firsts;
        let powers = |c: F128| Tail::Powers { c, ratio: F64::G };
        let arrays = vec![
            states.into(),
            nexts.into(),
            w_mem.into(),
            Array {
                head: y_mem,
                tail: powers(gm[0]),
            },
            w_bc.into(),
            Array {
                head: x_bc,
                tail: powers(x_g),
            },
            Array {
                head: Vec::new(),
                tail: Tail::Eq(ShiftEq::new(F128::ONE, F128::ZERO, ch.zeta.clone())),
            },
            Array {
                head: Vec::new(),
                tail: Tail::Eq(ShiftEq::new(F128::ZERO, F128::ONE, ch.zeta.clone())),
            },
            vec![payload].into(),
            v_word.into(),
            words.into(),
            w_fp.into(),
            p_fp.into(),
        ];
        let product = |coef, a, b| Term::Product { coef, a, b };
        let terms = [
            // The state identity: `eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j)`.
            product(F128::ONE, 6, 0),
            product(F128::ONE, 7, 1),
            product(ch.eta_mem, 2, 3),
            product(F128::ONE, 4, 5),
            Term::Single { coef: F128::ONE, a: 8 },
            product(ch.eta_mem, 9, 10),
            product(F128::ONE, 11, 12),
        ];
        let _rounds = tracing::info_span!("Index rounds").entered();
        index::prove(width, arrays, &terms, &mut |poly| {
            ps.add_round_poly(poly, false);
            ps.sample()
        })
    });

    // The memory term at `r`, then the fresh coefficients.
    let r = &index_end.point;
    let r_mem = &r[..log_mem];
    let below_mem = below_power(r, log_mem);
    let mem_values = mle_eval_many_par(&columns[MEMORY_0..=MEMORY_1], r_mem);
    // The word table at `r`.
    let m1 = (mem_values[0] + F128::Y * mem_values[1]) * below_mem;
    let y_mem_r = index_end.values[3];
    let x_bc_r = index_end.values[5];
    let p_fp_r = index_end.values[12];
    debug_assert_eq!(index_end.values[10], m1);
    debug_assert_eq!(
        y_mem_r,
        ch.gamma_mem[0] * primitives::field::index_mle(r) + ch.gamma_mem[3] * below_mem + ch.gamma_mem[1] * m1
    );
    #[cfg(test)]
    let m1 = m1 + cheat::MEMORY_TERM.get();
    ps.add_scalars(&[m1]);
    // The coefficients drawn after it, one per identity: the certificate's, then `JUMP`'s four.
    let [cert, jump_coefs @ ..]: [F128; 5] = ps.sample_packed(5).try_into().unwrap();
    let eq0_r = below_power(r, 0);
    // The state identity's weights at `r`, on `A` and on `B`.
    let (eq_zeta_r, shift_zeta_r) = (index_end.values[6], index_end.values[7]);

    let row_end = tracing::info_span!("Row side").in_scope(|| {
        let max_shift = plans.iter().map(|p| p.links.max_shift()).max().unwrap_or(0);
        let points = RowPoints::new(&chunks, r, max_shift);
        let mut q = 0;
        let mut tables_in = Vec::with_capacity(tables::N_TABLES);
        for t in 0..tables::N_TABLES {
            let (plan, cols) = (&plans[t], local(t));
            let ex = explicit[t];
            let pad = &padrows[t];
            // The cycle pointer's weight: the row's state and successor under the identity's weights at `r`.
            let weigh = |[state, next]: [F128; 2]| eq_zeta_r * state + shift_zeta_r * next;
            let mut aux = vec![tabulate(ex, |u| weigh(states_at(t, u)))];
            aux.extend(plan.gates.iter().map(|&g| tabulate(ex, |u| F128::from(cols[g][u]))));
            let s = &plan.links.state;
            let mut aux_tail = vec![weigh(state_forms[t].each_ref().map(|form| form.at(|c| pad[c])))];
            aux_tail.extend(plan.gates.iter().map(|&g| F128::from(pad[g])));
            // `fp`, the coefficient of the program side's `P_fp`, then each pointer's word reads' column part.
            let fp_aux = aux.len();
            aux.push(tabulate(ex, |u| F128::from(cols[s.fp][u])));
            aux_tail.push(F128::from(pad[s.fp]));
            let reads = word_reads(plan, all[t].n_committed_columns(), &ch.mu[t], F128::ONE);
            let mut read_aux = Vec::with_capacity(reads.len());
            for w in &reads {
                if w.read.cols.is_empty() {
                    read_aux.push(None);
                    continue;
                }
                read_aux.push(Some(aux.len()));
                let part = Affine {
                    constant: F128::ZERO,
                    cols: w.read.cols.clone(),
                };
                aux.push(tabulate(ex, |u| part.at(|c| cols[c][u])));
                aux_tail.push(part.at(|c| pad[c]));
            }
            let word_coef = ch.eta_mem * ch.gamma_mem[1] * m1;
            let mut row_columns = Vec::with_capacity(plan.pointers.len());
            for (k, &pointer) in plan.pointers.iter().enumerate() {
                let (omega, act, shifts) = match k {
                    0 => (
                        Coef::ZERO,
                        Coef {
                            constant: F128::ZERO,
                            aux: Some((0, F128::ONE)),
                        },
                        Vec::new(),
                    ),
                    1 => (
                        Coef {
                            constant: x_bc_r,
                            aux: Some((fp_aux, p_fp_r)),
                        },
                        Coef::ZERO,
                        Vec::new(),
                    ),
                    _ => {
                        let (mut omega, shifts) = plan.access_coefs(pointer, &ch.mu[t], ch.eta_mem * y_mem_r);
                        if let Some(i) = reads.iter().position(|w| w.pointer == pointer) {
                            omega.constant += word_coef * reads[i].read.constant;
                            if let Some(a) = read_aux[i] {
                                assert!(omega.aux.is_none(), "a gated pointer reads no word");
                                omega.aux = Some((a, word_coef));
                            }
                        }
                        (omega, Coef::ZERO, shifts)
                    }
                };
                row_columns.push(RowColumn {
                    words: primitives::cast_slice(cols[pointer]),
                    index: std::mem::take(&mut indices[t][k]),
                    omega,
                    act,
                    shifts,
                    cert: ch.eps[q].iter().map(|&e| cert * e).collect(),
                    q,
                });
                q += 1;
            }
            let jump = (all[t].n_constraints() > 0).then(|| eq_table(&ch.tau[..taus[t]]));
            let base = Base::new(
                blocks(all[t], plan, &ch, t, eq0_r, Some(jump_coefs)),
                cols.to_vec(),
                pad,
                jump,
            );
            tables_in.push(RowTable {
                log_rows: taus[t],
                rows: rows[t],
                explicit: ex,
                omega: std::mem::take(&mut omegas[t]),
                tau: ch.tau[..taus[t]].to_vec(),
                aux,
                aux_tail,
                columns: row_columns,
                base,
                base_first: base_firsts[t].map(|c| eq0_r * c),
            });
        }
        let q_vars = q.next_power_of_two().trailing_zeros() as usize;
        row::prove(
            &chunks,
            &points,
            tables_in,
            q_vars,
            // The row side continues the index side's claim.
            index_end.claim,
            &mut |poly| {
                ps.add_round_poly(poly, false);
                ps.sample()
            },
        )
    });

    // Each table's other columns at its row point, then the pointer columns' bit-slices.
    let chi = &row_end.point;
    let mut column_claims = Vec::new();
    let mut lanes = [F128::ZERO; primitives::hash::STATE_LANES];
    let column_values = tracing::info_span!("Column values").entered();
    // The values, then the slices, sent as one message, eight scalars a permutation.
    let mut message = Vec::new();
    for t in 0..tables::N_TABLES {
        let point = &chi[..taus[t]];
        let cols = local(t);
        let values = mle_eval_many_par(&plans[t].values.iter().map(|&c| cols[c]).collect::<Vec<_>>(), point);
        message.extend_from_slice(&values);
        for (&c, &value) in plans[t].values.iter().zip(&values) {
            let col = tables::GLOBAL_COLUMN_BASES[t] + c;
            match keccak_value(col) {
                Some(KeccakLane::Output(l)) => lanes[l] = value,
                _ => column_claims.push(ColumnClaim {
                    col,
                    point: point.to_vec(),
                    value,
                }),
            }
        }
    }
    drop(column_values);
    let eq_q = eq_table(&row_end.column_point);
    let mut slices = vec![F128::ZERO; 64];
    let mut pieces = Vec::new();
    let mut q = 0;
    // The row side's ends hold each pointer column's bit-slices at its table's row point.
    for t in 0..tables::N_TABLES {
        let point = &chi[..taus[t]];
        for (&pointer, end) in plans[t].pointers.iter().zip(&row_end.tables[t].columns) {
            for (s, &v) in slices.iter_mut().zip(&end.slices) {
                *s += eq_q[q] * v;
            }
            // The row side's bit-slices are the opening's first projection of the column's lane onto them, when
            // the column lies inside one lane.
            let placement = layout.rows_of(tables::GLOBAL_COLUMN_BASES[t] + pointer, taus[t]);
            pieces.push(RingPiece {
                offset: placement.offset,
                point: point.to_vec(),
                scale: eq_q[q],
                slices: (placement.n_vars <= layout.shape.mu - crate::pcs::LOG_BATCH).then(|| end.slices.clone()),
            });
            q += 1;
        }
    }
    message.extend_from_slice(&slices);
    ps.add_scalars_packed(&message);
    let memory = StackClaim::Sum {
        parts: (MEMORY_0..=MEMORY_1)
            .map(|c| layout.placements[c].sum_part(r_mem.to_vec(), [F128::ONE, F128::Y][c - MEMORY_0] * below_mem))
            .collect(),
        value: m1,
    };
    LinkEnd {
        memory,
        columns: column_claims,
        ring: RingSwitchClaim {
            pieces,
            s_hat_v: Some(slices),
        },
        output: keccak_gkr::OutputClaim {
            instance: chi[..taus[verifier::layout::OP_KECCAK]].to_vec(),
            lanes,
        },
    }
}

/// Test-only ways for the prover to cheat past its witness, for the negative tests: the word the index side scatters
/// for one row of one pointer column, and a change to the memory term it sends.
#[cfg(test)]
pub(crate) mod cheat {
    use primitives::field::F128;
    use std::cell::Cell;

    thread_local! {
        /// `(table, local column, row, word)`: the index side scatters `word` for that row instead of its own.
        pub(crate) static INDEX_WORD: Cell<Option<(usize, usize, usize, u64)>> = const { Cell::new(None) };
        /// Added to `M_1` before it is sent.
        pub(crate) static MEMORY_TERM: Cell<F128> = const { Cell::new(F128::ZERO) };
    }
}
