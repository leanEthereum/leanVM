//! Hotwire's prover: the challenges, the index side, the row side and the claims they leave on the commitment.
//!
//! After the commitment the verifier draws the link challenges. The index side runs over `j < 2^W` on arrays the
//! pointers scatter, then the prover sends the memory term `M_1` at its end `r`, and the verifier draws one fresh
//! coefficient per identity. The row side then continues the same claim over every table's rows and the pointer
//! columns. It ends with each table's non-pointer columns at its row point and the 64 bit-slices of the pointer
//! columns, which become point claims and one ring-switched claim.

use super::base::{Base, Block, Weight};
use super::index::{self, Array, Scatter, ShiftEq, Tail, Term};
use super::pointer::Chunks;
use super::row::{self, Coef, RowColumn, RowPoints, RowTable, ShiftGroup};
use crate::cpu::{KeccakLane, Layout, keccak_value};
use crate::form::Form;
use crate::tables::{self, GLOBAL_COLUMN_BASES, Links, N_TABLES, Table};
use crate::witness::mle_eval_cols;
use ::pcs::{RingPiece, RingSwitchClaim, StackClaim};
use primitives::field::{F64, F128, g_pow, index_mle};
use primitives::multilinear::eq_table;
use primitives::transcript::ProverState;
use std::borrow::Cow;
use verifier::layout::{BYTECODE_SLOT_BITS, MEMORY_0, MEMORY_1, OP_KECCAK, OPCODE_SLOT};

/// Entries per task when tabulating an array over the index.
const TASK: usize = 1 << 12;

/// What a table links, and how Hotwire reads its columns.
pub(crate) struct Plan {
    pub links: Links,
    /// The columns that gate an access, in order of first use.
    pub gates: Vec<usize>,
    /// Every other column, in local order: what the prover sends at the row point.
    pub values: Vec<usize>,
}

impl Plan {
    pub(crate) fn of(table: &dyn Table) -> Self {
        let links = table.links();
        let mut gates = Vec::new();
        for g in links.memory.iter().filter_map(|a| a.gate) {
            if !gates.contains(&g) {
                gates.push(g);
            }
        }
        let values = (0..table.n_committed_columns())
            .filter(|c| !links.pointers().contains(c))
            .collect();
        Self { links, gates, values }
    }

    /// The aux index of a gate column on the row side: the state form comes first.
    fn gate_aux(&self, gate: usize) -> usize {
        1 + self.gates.iter().position(|&g| g == gate).expect("a gate")
    }

    /// A pointer column's coefficient on `ω_F` from the access it takes unshifted, and its shift groups, one per gate,
    /// from the accesses it takes shifted; `c` is `η_mem·Y(r)`.
    fn access_coefs(&self, pointer: usize, mu: &[F128], c: F128) -> (Coef, Vec<ShiftGroup>) {
        let coef = |gate: Option<usize>, mu: F128| match gate {
            None => Coef::constant(c * mu),
            Some(g) => Coef {
                constant: F128::ZERO,
                aux: Some((self.gate_aux(g), c * mu)),
            },
        };
        let mut omega = None;
        let mut groups: Vec<(Option<usize>, ShiftGroup)> = Vec::new();
        for (access, &mu) in self.links.memory.iter().zip(mu) {
            if access.pointer != pointer {
                continue;
            }
            if access.shift == 0 {
                assert!(omega.is_none(), "one unshifted access per pointer");
                omega = Some(coef(access.gate, mu));
                continue;
            }
            match groups.iter_mut().find(|(g, _)| *g == access.gate) {
                Some((_, group)) => group.weights.push((access.shift, mu)),
                None => groups.push((
                    access.gate,
                    ShiftGroup {
                        coef: coef(access.gate, F128::ONE),
                        weights: vec![(access.shift, mu)],
                    },
                )),
            }
        }
        let groups = groups.into_iter().map(|(_, g)| g).collect();
        (omega.unwrap_or(Coef::ZERO), groups)
    }
}

/// The link challenges, drawn after the commitment (`verifier::link::verify_link`).
pub(crate) struct Challenges {
    pub theta: Vec<F128>,
    pub tau: Vec<F128>,
    /// On `pc`, `fp`.
    pub gamma_state: [F128; 2],
    /// On the address, the two limbs (`γ_word` and `γ_word·y`) and the presence coordinate.
    pub gamma_mem: [F128; 4],
    /// Per table, per access.
    pub mu: Vec<Vec<F128>>,
    /// `eq(α, s)` over the `2^BYTECODE_SLOT_BITS` slots of the stacked program.
    pub alpha_bc: Vec<F128>,
    pub zeta: Vec<F128>,
    pub eta_mem: F128,
    pub eta_bc: F128,
    /// Per pointer column, in Hotwire's order across the tables, per chunk: `ε_q·ν_c`.
    pub eps: Vec<Vec<F128>>,
}

impl Challenges {
    /// After the grind their error asks for ([`verifier::link_grind_bits`]). The grind's permutation draws `θ_0`; the
    /// rest come eight to a permutation, the ones whose count is fixed first.
    pub(crate) fn sample(ps: &mut ProverState, plans: &[Plan], taus: &[usize], chunks: &Chunks) -> Self {
        let m = taus.iter().copied().max().unwrap_or(0);
        ps.grind(verifier::link_grind_bits(m, chunks.width));
        let mut theta = vec![ps.sample()];
        let n = verifier::packed_challenges(tables::layout_tables(), m, chunks.width);
        let mut drawn = ps.sample_packed(n).into_iter();
        let mut take = |n: usize| -> Vec<F128> { drawn.by_ref().take(n).collect() };
        theta.extend(take(N_TABLES - 1));
        let gamma_state: [F128; 2] = take(2).try_into().unwrap();
        // A word `lo + y·hi` takes `γ_word·y` on its high limb.
        let [g_addr, g_word, g_pres]: [F128; 3] = take(3).try_into().unwrap();
        let gamma_mem = [g_addr, g_word, g_word * F128::Y, g_pres];
        let mu = plans.iter().map(|p| take(p.links.memory.len())).collect();
        let alpha_bc = take(BYTECODE_SLOT_BITS);
        let [eta_mem, eta_bc]: [F128; 2] = take(2).try_into().unwrap();
        let n_pointers: usize = plans.iter().map(|p| p.links.pointers().len()).sum();
        let eps = take(n_pointers);
        let tau = take(m);
        let zeta = take(chunks.width);
        let nu = take(chunks.d());
        assert!(drawn.next().is_none(), "every packed challenge is taken");
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

/// A table's payload forms, before the `eq(0, r)` factor: the ungated part `η_mem·Σ μ·access + η_bc·R_bc`, then one
/// form per gate, `η_mem·Σ μ·access` over the accesses it gates. An access's committed part is `γ_addr·address +
/// γ_pres + γ_word·value`; its reads are weighed on the side of the link that holds them.
fn payload_forms(table: &dyn Table, plan: &Plan, ch: &Challenges, t: usize) -> (Form, Vec<Form>) {
    let n = table.n_committed_columns();
    let (a, links) = (&ch.alpha_bc, &plan.links);
    let bc = &links.bytecode;
    let mut ungated = Form::new(n);
    ungated.coeffs[bc.pc] += ch.eta_bc * a[1];
    ungated.constant += ch.eta_bc * a[2] + (ch.eta_bc * a[3]).mul_base(g_pow(bc.opcode));
    for (slots, operand) in &bc.operands {
        ungated.add_scaled(operand, ch.eta_bc * a[slots[0]]);
    }
    let mut gated: Vec<Form> = plan.gates.iter().map(|_| Form::new(n)).collect();
    for (access, &mu) in links.memory.iter().zip(&ch.mu[t]) {
        let form = match access.gate {
            None => &mut ungated,
            Some(g) => &mut gated[plan.gate_aux(g) - 1],
        };
        let w = ch.eta_mem * mu;
        form.add_scaled(&access.address, w * ch.gamma_mem[0]);
        form.constant += w * ch.gamma_mem[3];
        form.add_scaled(&access.value, w * ch.gamma_mem[1]);
    }
    (ungated, gated)
}

/// A table's base blocks, the payload's forms scaled by `scale`, and `JUMP`'s identities on every row under `jump`.
fn blocks(table: &dyn Table, plan: &Plan, ch: &Challenges, t: usize, scale: F128, jump: Option<&[F128]>) -> Vec<Block> {
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
    if let Some(coefs) = jump.filter(|_| table.n_constraints() > 0) {
        out.push(Block {
            weight: Weight::Eq,
            gate: None,
            form: table.constraint(coefs),
        });
    }
    out
}

/// One past the last row that differs from the padrow in any column, at least `rows`, even, at most `2^log_rows`.
fn explicit_rows(columns: &[&[F64]], padrow: &[F64], rows: usize, log_rows: usize) -> usize {
    let last = parallel::map_collect(columns.len(), |c| {
        let col = columns[c];
        (0..col.len()).rev().find(|&u| col[u] != padrow[c]).map_or(0, |u| u + 1)
    });
    let e = last.into_iter().max().unwrap_or(0).max(rows);
    (e + (e & 1)).min(1 << log_rows)
}

/// `f(j, g^j)` for `j < n`, in parallel: each task seeds `g^j` once and steps it by `g`.
fn tabulate_powers(n: usize, f: impl Fn(usize, F64) -> F128 + Sync) -> Vec<F128> {
    let mut out = parallel::filled(n, F128::ZERO);
    parallel::chunks_mut(&mut out, TASK, |task, chunk| {
        let start = task * TASK;
        let mut g = g_pow(start);
        for (k, o) in chunk.iter_mut().enumerate() {
            *o = f(start + k, g);
            g *= F64::G;
        }
    });
    out
}

/// `Π_{h ≥ k} (1 + x_h)`: the multilinear extension of `[j < 2^k]`, the spec's `LT_{2^k}`.
pub(crate) fn below_power(point: &[F128], k: usize) -> F128 {
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
        let zero = [F128::ZERO; 1 << BYTECODE_SLOT_BITS];
        let mut w = Self {
            omega: vec![zero; plans.len()],
            pc: vec![zero; plans.len()],
            frame: vec![zero; plans.len()],
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
                    w.frame[t][s] += (m * gm[0]).mul_base(g_pow(e as usize));
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

/// A table's reads of the word at one pointer, `Σ μ·scale` over its accesses, times `weight`: an affine form.
struct WordReads {
    pointer: usize,
    scale: Form,
}

/// Each pointer a table reads words at, with what it reads there under `weight·μ`.
fn word_reads(plan: &Plan, n_cols: usize, mu: &[F128], weight: F128) -> Vec<WordReads> {
    let mut out: Vec<WordReads> = Vec::new();
    for (access, &mu) in plan.links.memory.iter().zip(mu) {
        for read in &access.reads {
            let tables::Read::Word { pointer, scale } = read else {
                continue;
            };
            assert!(scale.is_affine(), "a word read's scale is affine");
            let at = match out.iter().position(|w| w.pointer == *pointer) {
                Some(at) => at,
                None => {
                    out.push(WordReads {
                        pointer: *pointer,
                        scale: Form::new(n_cols),
                    });
                    out.len() - 1
                }
            };
            out[at].scale.add_scaled(scale, weight * mu);
        }
    }
    out
}

/// The words of table `t`'s pointer column `column` that the index side scatters: the column's own, unless a test
/// cheats ([`cheat::INDEX_WORD`]).
fn index_words(t: usize, column: usize, words: &[u64]) -> Cow<'_, [u64]> {
    #[cfg(test)]
    if let Some((ct, cc, u, word)) = cheat::INDEX_WORD.get()
        && (ct, cc) == (t, column)
        && u < words.len()
    {
        let mut words = words.to_vec();
        words[u] = word;
        return Cow::Owned(words);
    }
    let _ = (t, column);
    Cow::Borrowed(words)
}

/// A claim the link leaves on a non-pointer column: the global column, at its table's row point.
pub(crate) struct ColumnClaim {
    pub col: usize,
    pub point: Vec<F128>,
}

/// What the link leaves on the commitment: the memory term, each table's non-pointer columns at its row point, the
/// pointer columns' ring-switched claim, and the Keccak reduction's claim on the permutation's output.
pub(crate) struct LinkEnd {
    /// The memory term at `r`, `M_1`: both limbs of the memory at `r_mem`, scaled by `below_mem` and `y·below_mem`.
    pub memory: StackClaim,
    /// In table order, each table's in local order, the output lanes left out.
    pub columns: Vec<ColumnClaim>,
    /// One piece per pointer column, in Hotwire's order across the tables.
    pub ring: RingSwitchClaim,
    pub output: keccak_gkr::OutputClaim,
}

/// Prove the links of an execution whose columns are `columns` (every global column, virtual ones included), of
/// `layout`, running `program`, the stacked bytecode.
pub(crate) fn prove(ps: &mut ProverState, layout: &Layout, columns: &[&[F64]], program: &[u64]) -> LinkEnd {
    let chunks = Chunks::new(layout.pointer_width);
    let width = chunks.width;
    let n = 1usize << width;
    let all = tables::tables();
    let plans: Vec<Plan> = all.iter().map(|&t| Plan::of(t)).collect();
    let (taus, rows) = (layout.taus, layout.rows);
    let local = |t: usize| &columns[GLOBAL_COLUMN_BASES[t]..GLOBAL_COLUMN_BASES[t] + all[t].n_committed_columns()];
    let ch = Challenges::sample(ps, &plans, &taus, &chunks);
    let weights = SlotWeights::new(&plans, &ch);
    let cycles: usize = rows.iter().sum();
    let log_mem = layout.placements[MEMORY_0].n_vars;
    // The stacked program: slot `s` of instruction `j` is `program[s·bytecode_size + j]`.
    let bytecode_size = program.len() >> BYTECODE_SLOT_BITS;
    let slot = |s: usize, j: usize| F64(program[s * bytecode_size + j]);

    // `ω_F = θ_F·eq(τ_F, u)` on each table's executed rows.
    let omegas: Vec<Vec<F128>> = (0..N_TABLES)
        .map(|t| {
            let mut e = eq_table(&ch.tau[..taus[t]]);
            e.truncate(rows[t]);
            parallel::map_collect(e.len(), |u| ch.theta[t] * e[u])
        })
        .collect();
    let padrows: Vec<Vec<F64>> = all.iter().map(|t| t.padding()).collect();
    let explicit: Vec<usize> = (0..N_TABLES)
        .map(|t| explicit_rows(local(t), &padrows[t], rows[t], taus[t]))
        .collect();
    // Each table's state `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp` and successor `ŝ'_γ`, affine in its columns.
    let state_forms: Vec<[Form; 2]> = (0..N_TABLES)
        .map(|t| {
            let s = &plans[t].links.state;
            let mut state = Form::new(all[t].n_committed_columns());
            state.constant = F128::ONE;
            let mut next = state.clone();
            state.coeffs[s.pc] += ch.gamma_state[0];
            state.coeffs[s.fp] += ch.gamma_state[1];
            next.add_scaled(&s.next[0], ch.gamma_state[0]);
            next.add_scaled(&s.next[1], ch.gamma_state[1]);
            assert!(next.is_affine(), "a state link is affine");
            [state, next]
        })
        .collect();
    let states_at = |t: usize, u: usize| {
        let cols = local(t);
        state_forms[t].each_ref().map(|form| form.evaluate_k(|c| cols[c][u]))
    };

    let index_end = tracing::info_span!("Index side").in_scope(|| {
        let scatter = tracing::info_span!("Scatter").entered();
        // Each table's pointer columns' words, in `Links::pointers` order.
        let words: Vec<Vec<Cow<[u64]>>> = (0..N_TABLES)
            .map(|t| {
                (plans[t].links.pointers().iter())
                    .map(|&c| index_words(t, c, primitives::cast_slice(local(t)[c])))
                    .collect()
            })
            .collect();
        let pointer = |t: usize, c: usize| {
            let k = (plans[t].links.pointers().iter())
                .position(|&p| p == c)
                .expect("a pointer column");
            &*words[t][k]
        };
        // `A` and `B`, each row's state and successor at its cycle; the memory accesses' weights at their cells; the
        // word reads' at the cells they read; the rows' weight and `ω·fp` at their instructions.
        let fill = |lens: [usize; 6]| {
            let arrays = lens.map(Scatter::new);
            let [states, nexts, w_mem, v_word, w_bc, w_fp] = &arrays;
            for t in 0..N_TABLES {
                let (plan, cols, omega, n_t) = (&plans[t], local(t), &omegas[t], rows[t]);
                let cycle = pointer(t, plan.links.state.cycle);
                index::add_words(&chunks, cycle, n_t, &[(states, 0), (nexts, 0)], |u, w| {
                    w.copy_from_slice(&states_at(t, u));
                });
                // Each pointer's accesses at their shifts, then its word read.
                let reads = word_reads(plan, cols.len(), &ch.mu[t], ch.gamma_mem[1]);
                for &p in plan.links.pointers() {
                    let accesses: Vec<_> = (plan.links.memory.iter().zip(&ch.mu[t]))
                        .filter(|(a, _)| a.pointer == p)
                        .collect();
                    let read = reads.iter().find(|r| r.pointer == p);
                    let mut targets: Vec<(&Scatter, usize)> = accesses.iter().map(|(a, _)| (w_mem, a.shift)).collect();
                    targets.extend(read.map(|_| (v_word, 0)));
                    if targets.is_empty() {
                        continue;
                    }
                    index::add_words(&chunks, pointer(t, p), n_t, &targets, |u, w| {
                        for (w, &(access, &mu)) in w.iter_mut().zip(&accesses) {
                            let m = mu * omega[u];
                            *w = access.gate.map_or(m, |g| m.mul_base(cols[g][u]));
                        }
                        if let Some(read) = read {
                            w[accesses.len()] = read.scale.evaluate_k(|c| cols[c][u]) * omega[u];
                        }
                    });
                }
                let (bc, fp) = (pointer(t, plan.links.bytecode.pointer), cols[plan.links.state.fp]);
                index::add_words(&chunks, bc, n_t, &[(w_bc, 0), (w_fp, 0)], |u, w| {
                    w.copy_from_slice(&[omega[u], omega[u].mul_base(fp[u])]);
                });
            }
            arrays
        };
        // Sized for an honest execution's indices: cycles, memory cells and instructions. An index past these makes
        // the arrays again at the full `2^W`.
        let lens = [cycles, cycles, 1 << log_mem, 1 << log_mem, bytecode_size, bytecode_size];
        let mut arrays = fill(lens.map(|l| l.min(n)));
        if arrays.iter().any(Scatter::overflowed) {
            arrays = fill([n; 6]);
        }
        let [states, nexts, w_mem, v_word, w_bc, w_fp] = arrays.map(Scatter::into_vec);
        drop(scatter);

        let _tables = tracing::info_span!("Index tables").entered();
        let gm = ch.gamma_mem;
        let mem = [columns[MEMORY_0], columns[MEMORY_1]];
        // The memory's address table `Y = γ_addr·g^j + γ_word·word(j) + γ_pres` and word table `lo + y·hi`, over its
        // cells; past them only `γ_addr·g^j` is left, and no word.
        let y_mem = tabulate_powers(1 << log_mem, |j, g_j| {
            gm[0].mul_base(g_j) + gm[1].mul_base(mem[0][j]) + gm[2].mul_base(mem[1][j]) + gm[3]
        });
        let words = parallel::map_collect(1 << log_mem, |j| F128::new(mem[0][j].0, mem[1][j].0));
        // The program side's targets: `X_ω` under the rows' weight and `P_fp` under `ω·fp`, each weighing an
        // instruction's slots by its opcode.
        let a = &ch.alpha_bc;
        let (x_g, x_one) = (ch.eta_bc * a[1], ch.eta_bc * a[2]);
        let opcode = |j: usize| slot(OPCODE_SLOT, j).0.trailing_zeros() as usize;
        // Each opcode's slots of nonzero weight.
        let read: Vec<Vec<usize>> = (0..N_TABLES)
            .map(|op| {
                (OPCODE_SLOT..1 << BYTECODE_SLOT_BITS)
                    .filter(|&s| {
                        [&weights.omega, &weights.pc, &weights.frame]
                            .iter()
                            .any(|w| !w[op][s].is_zero())
                    })
                    .collect()
            })
            .collect();
        let x_bc = tabulate_powers(bytecode_size, |j, g_j| {
            let op = opcode(j);
            let mut x = x_g.mul_base(g_j) + x_one;
            for &s in &read[op] {
                x += weights.omega[op][s].mul_base(slot(s, j)) + weights.pc[op][s].mul_base(g_j * slot(s, j));
            }
            x
        });
        let p_fp = parallel::map_collect(bytecode_size, |j| {
            let op = opcode(j);
            (read[op].iter().filter(|&&s| s > OPCODE_SLOT))
                .map(|&s| weights.frame[op][s].mul_base(slot(s, j)))
                .sum()
        });
        // The base terms' `ω` blocks over the rows: the index side's constant payload.
        let payload: F128 = (0..N_TABLES)
            .map(|t| {
                let base = Base::new(
                    blocks(all[t], &plans[t], &ch, t, F128::ONE, None),
                    local(t),
                    &padrows[t],
                    rows[t],
                    None,
                );
                base.payload(&omegas[t])
            })
            .sum();
        drop(_tables);

        let powers = |head: Vec<F128>, c: F128| Array {
            head,
            tail: Tail::Powers { c, ratio: F64::G },
        };
        let eq = |a: F128, b: F128| Array {
            head: Vec::new(),
            tail: Tail::Eq(ShiftEq::new(a, b, ch.zeta.clone())),
        };
        let arrays = vec![
            states.into(),
            nexts.into(),
            w_mem.into(),
            powers(y_mem, gm[0]),
            w_bc.into(),
            powers(x_bc, x_g),
            eq(F128::ONE, F128::ZERO),
            eq(F128::ZERO, F128::ONE),
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
    let mem_values = mle_eval_cols(&columns[MEMORY_0..=MEMORY_1], r_mem);
    let m1 = (mem_values[0] + F128::Y * mem_values[1]) * below_mem;
    let (y_mem_r, x_bc_r, p_fp_r) = (index_end.values[3], index_end.values[5], index_end.values[12]);
    debug_assert_eq!(index_end.values[10], m1);
    debug_assert_eq!(
        y_mem_r,
        ch.gamma_mem[0] * index_mle(r) + ch.gamma_mem[3] * below_mem + ch.gamma_mem[1] * m1
    );
    #[cfg(test)]
    let m1 = m1 + cheat::MEMORY_TERM.get();
    ps.add_scalars(&[m1]);
    let [cert, jump @ ..]: [F128; 5] = ps.sample_packed(5).try_into().unwrap();
    let eq0_r = below_power(r, 0);
    // The state identity's weights at `r`, on `A` and on `B`.
    let (eq_zeta_r, shift_zeta_r) = (index_end.values[6], index_end.values[7]);

    let row_end = tracing::info_span!("Row side").in_scope(|| {
        let max_shift = plans.iter().map(|p| p.links.max_shift()).max().unwrap_or(0);
        let points = RowPoints::new(&chunks, r, max_shift);
        let mut q = 0;
        let mut tables_in = Vec::with_capacity(N_TABLES);
        for (t, omega) in omegas.into_iter().enumerate() {
            let (plan, cols, pad, ex) = (&plans[t], local(t), &padrows[t], explicit[t]);
            let pad_row = |c: usize| pad[c];
            // The linear forms the coefficients name, on the explicit rows and the padrow: the cycle pointer's weight
            // (the row's state and successor under the identity's weights at `r`), each gate, `fp` (the coefficient
            // of the program side's `P_fp`), then each pointer's word reads' column part.
            let weigh = |[state, next]: [F128; 2]| eq_zeta_r * state + shift_zeta_r * next;
            let mut aux = vec![parallel::map_collect(ex, |u| weigh(states_at(t, u)))];
            let mut aux_tail = vec![weigh(state_forms[t].each_ref().map(|f| f.evaluate_k(pad_row)))];
            let column_aux = |c: usize| parallel::map_collect(ex, |u| F128::from(cols[c][u]));
            for &g in &plan.gates {
                aux.push(column_aux(g));
                aux_tail.push(F128::from(pad[g]));
            }
            let fp = plan.links.state.fp;
            let fp_aux = aux.len();
            aux.push(column_aux(fp));
            aux_tail.push(F128::from(pad[fp]));
            let reads = word_reads(plan, cols.len(), &ch.mu[t], F128::ONE);
            let mut read_aux = Vec::with_capacity(reads.len());
            for w in &reads {
                let mut linear = w.scale.clone();
                linear.constant = F128::ZERO;
                if linear.coeffs.iter().all(|c| c.is_zero()) {
                    read_aux.push(None);
                    continue;
                }
                read_aux.push(Some(aux.len()));
                aux.push(parallel::map_collect(ex, |u| linear.evaluate_k(|c| cols[c][u])));
                aux_tail.push(linear.evaluate_k(pad_row));
            }
            let word_coef = ch.eta_mem * ch.gamma_mem[1] * m1;
            let mut row_columns = Vec::with_capacity(plan.links.pointers().len());
            for (k, &pointer) in plan.links.pointers().iter().enumerate() {
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
                            omega.constant += word_coef * reads[i].scale.constant;
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
                    omega,
                    act,
                    shifts,
                    cert: ch.eps[q].iter().map(|&e| cert * e).collect(),
                    q,
                });
                q += 1;
            }
            let eq_tau = (all[t].n_constraints() > 0).then(|| eq_table(&ch.tau[..taus[t]]));
            let base = Base::new(
                blocks(all[t], plan, &ch, t, eq0_r, Some(&jump[..])),
                cols,
                pad,
                ex,
                eq_tau,
            );
            tables_in.push(RowTable {
                log_rows: taus[t],
                rows: rows[t],
                explicit: ex,
                omega,
                aux,
                aux_tail,
                columns: row_columns,
                base,
            });
        }
        row::prove(
            &chunks,
            &points,
            tables_in,
            crate::log2_ceil_usize(q),
            index_end.claim,
            &mut |poly| {
                ps.add_round_poly(poly, false);
                ps.sample()
            },
        )
    });

    // Each table's other columns at its row point, then the pointer columns' bit-slices, sent as one message.
    let chi = &row_end.point;
    let mut column_claims = Vec::new();
    let mut lanes = [F128::ZERO; primitives::hash::STATE_LANES];
    let mut message = Vec::new();
    tracing::info_span!("Column values").in_scope(|| {
        for t in 0..N_TABLES {
            let point = &chi[..taus[t]];
            let cols: Vec<&[F64]> = plans[t].values.iter().map(|&c| local(t)[c]).collect();
            let values = mle_eval_cols(&cols, point);
            message.extend_from_slice(&values);
            for (&c, &value) in plans[t].values.iter().zip(&values) {
                let col = GLOBAL_COLUMN_BASES[t] + c;
                match keccak_value(col) {
                    Some(KeccakLane::Output(l)) => lanes[l] = value,
                    _ => column_claims.push(ColumnClaim {
                        col,
                        point: point.to_vec(),
                    }),
                }
            }
        }
    });
    let eq_q = eq_table(&row_end.column_point);
    let mut slices = vec![F128::ZERO; 64];
    let mut pieces = Vec::new();
    let mut q = 0;
    for t in 0..N_TABLES {
        let point = &chi[..taus[t]];
        for (&pointer, end) in plans[t].links.pointers().iter().zip(&row_end.tables[t].columns) {
            for (s, &v) in slices.iter_mut().zip(&end.slices) {
                *s += eq_q[q] * v;
            }
            pieces.push(RingPiece {
                offset: layout.rows_of(GLOBAL_COLUMN_BASES[t] + pointer, taus[t]).offset,
                point: point.to_vec(),
                scale: eq_q[q],
            });
            q += 1;
        }
    }
    message.extend_from_slice(&slices);
    ps.add_scalars_packed(&message);
    let memory = StackClaim::Sum {
        parts: [(MEMORY_0, F128::ONE), (MEMORY_1, F128::Y)]
            .map(|(c, y)| layout.placements[c].sum_part(r_mem.to_vec(), y * below_mem))
            .into(),
    };
    LinkEnd {
        memory,
        columns: column_claims,
        ring: RingSwitchClaim { pieces },
        output: keccak_gkr::OutputClaim {
            instance: chi[..taus[OP_KECCAK]].to_vec(),
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `[j < 2^k]` at boolean points.
    #[test]
    fn below_power_is_the_prefix_indicator() {
        for n in 0..5 {
            for k in 0..=n + 1 {
                for j in 0..1usize << n {
                    let point: Vec<F128> = (0..n).map(|h| F128::new((j >> h & 1) as u64, 0)).collect();
                    let expected = if j < 1 << k { F128::ONE } else { F128::ZERO };
                    assert_eq!(below_power(&point, k), expected, "n {n}, k {k}, j {j}");
                }
            }
        }
    }
}
