//! The verifier core up to the flock reductions, as rows: the announcement, the bus's grand products and
//! their decomposition, the table sumcheck, the program claim, and the claims the opening discharges.

use super::math::{eq_bits, eq_table, int_index_mle, interp, poly_eval, product, times_one_plus};
use super::{ProgramClaim, StackClaim};
use crate::cpu::{Framework, Layout, Schema, Shared};
use crate::leaf::{Block, Coord, N_TUPLE_BITS, Producer};
use crate::rec::circuit::{Builder, Ew};
use crate::rec::transcript::Transcript;
use crate::rv::{Reg, RegisterFile, Syscall};
use crate::tables::{CYCLE, LIVE_BIT, N_TABLES};
use crate::witness::Placement;
use primitives::field::F192;
use std::collections::HashMap;

/// A column claim on the inner stack.
pub(super) struct ColumnClaim {
    col: usize,
    point: Vec<Ew>,
    value: Ew,
}

/// A table's block on one side, kept symbolic until its columns' values are read: its selector and its tuple.
struct FormBlock {
    side: usize,
    selector: Ew,
    coords: Vec<Coord>,
}

/// RAM's image's share of a side's leaf claim, which the program claim settles.
struct SparseShare {
    side: usize,
    weight: Ew,
    point: Vec<Ew>,
}

/// What the bus leaves (`leaf::BusVerify`).
pub(super) struct Bus {
    pub(super) claims: Vec<ColumnClaim>,
    point: Vec<Ew>,
    forms: Vec<Vec<FormBlock>>,
    producers: Vec<Vec<Ew>>,
    totals: [Ew; 2],
    sparse: Vec<SparseShare>,
    alphas: Vec<Ew>,
    weights: Vec<Ew>,
    beta: Ew,
}

/// `gkr::verify_products::<2>`: the two sides' grand products under one root, reduced to their leaf
/// vectors at one point.
pub(crate) fn verify_products(b: &mut Builder, t: &mut Transcript, mu: usize) -> (Vec<Ew>, [Ew; 2]) {
    let root = t.next_scalar(b);
    let mut values = [root, root];
    let mut lambda = t.sample(b);
    let mut point: Vec<Ew> = Vec::new();
    let mut layer = mu;
    while layer > 0 {
        let round_count = mu - layer;
        let mut claim = poly_eval(b, &values, lambda);
        if layer % 2 == 1 {
            let tails: Vec<[Ew; 2]> = (0..2).map(|_| [t.next_scalar(b), t.next_scalar(b)]).collect();
            let products: Vec<Ew> = tails.iter().map(|&[l, r]| b.mul(l, r)).collect();
            let expected = poly_eval(b, &products, lambda);
            b.eq_e(claim, expected);
            let challenge = t.sample(b);
            for (value, &[l, r]) in values.iter_mut().zip(&tails) {
                *value = interp(b, l, r, challenge);
            }
            lambda = t.sample(b);
            point = vec![challenge];
            layer -= 1;
            continue;
        }
        let mut round_point = Vec::with_capacity(round_count);
        for &eq_point in point.iter().take(round_count) {
            let h = t.next_round_poly(b, 5, claim, Some(eq_point));
            let challenge = t.sample(b);
            round_point.push(challenge);
            claim = poly_eval(b, &h, challenge);
        }
        let tails: Vec<[Ew; 4]> = (0..2).map(|_| std::array::from_fn(|_| t.next_scalar(b))).collect();
        let products: Vec<Ew> = tails.iter().map(|tail| product(b, tail)).collect();
        let expected = poly_eval(b, &products, lambda);
        b.eq_e(claim, expected);
        let low = t.sample(b);
        let high = t.sample(b);
        for (value, tail) in values.iter_mut().zip(&tails) {
            let a = interp(b, tail[0], tail[1], low);
            let c = interp(b, tail[2], tail[3], low);
            *value = interp(b, a, c, high);
        }
        lambda = t.sample(b);
        point = vec![low, high];
        point.extend(round_point);
        layer -= 2;
    }
    (point, values)
}

/// `leaf::verify_balance` on the inner layout. The final state's clock is the wire `ts`: the layout was
/// built with zero there, the only coordinate the announcement fixes.
pub(super) fn verify_balance(b: &mut Builder, t: &mut Transcript, l: &Layout, ts: Ew) -> Bus {
    let spans = &Schema::get().spans;
    let mut push_lay = crate::leaf::layout(&l.push, &l.producers);
    let mut pull_lay = crate::leaf::layout(&l.pull, &[]);
    let mu = push_lay.mu.max(pull_lay.mu);
    (push_lay.mu, pull_lay.mu) = (mu, mu);
    let alphas = t.sample_vec(b, N_TUPLE_BITS);
    let weights = eq_table(b, &alphas);
    let beta = t.sample(b);
    let (point, values) = verify_products(b, t, mu);

    let mut forms: Vec<Vec<FormBlock>> = (0..N_TABLES).map(|_| Vec::new()).collect();
    let mut claims: Vec<ColumnClaim> = Vec::new();
    let mut known: HashMap<(usize, usize), Ew> = HashMap::new();
    let mut producers = Vec::new();
    let mut sparse = Vec::new();
    let mut totals = [beta; 2];
    let sides: [(&[Block], &[Producer], &crate::leaf::Layout); 2] =
        [(&l.push, &l.producers, &push_lay), (&l.pull, &[], &pull_lay)];
    for (s, (blocks, side_producers, lay)) in sides.into_iter().enumerate() {
        let selector =
            |b: &mut Builder, block: usize, kappa: usize| eq_bits(b, lay.offsets[block] >> kappa, &point[kappa..mu]);
        let mut sel_terms: Vec<Ew> = Vec::new();
        let mut index = blocks.len();
        for p in side_producers {
            let sels: Vec<Ew> = (index..index + p.bits).map(|i| selector(b, i, p.kappa)).collect();
            sel_terms.extend(&sels);
            producers.push(sels);
            index += p.bits;
        }
        let mut acc = b.zero();
        for (i, block) in blocks.iter().enumerate() {
            let kappa = block.kappa;
            let zeta_lo = &point[..kappa];
            let eq_hi = selector(b, i, kappa);
            sel_terms.push(eq_hi);
            if let Some(owner) = block.owner {
                forms[owner].push(FormBlock {
                    side: s,
                    selector: eq_hi,
                    coords: block.coords.iter().map(|c| local(c, spans[owner].0)).collect(),
                });
                continue;
            }
            let is_final_state = s == 1 && i == Framework::State as usize;
            let mut inner = b.zero();
            for (j, c) in block.coords.iter().enumerate() {
                let w = weights[j];
                inner = match c {
                    Coord::Const(v) if is_final_state && j >= 2 => {
                        debug_assert_eq!(v.0, 0, "the layout's final clock is a placeholder");
                        b.mul_add(w, ts, inner)
                    }
                    Coord::Const(v) => b.mul_const_add(w, F192::from(*v), inner),
                    Coord::IntIndex { base, shift } => {
                        let x = int_index_mle(b, base.0, *shift, zeta_lo);
                        b.mul_add(w, x, inner)
                    }
                    Coord::Col(col) => {
                        let value = *known.entry((*col, kappa)).or_insert_with(|| {
                            let v = t.next_scalar(b);
                            claims.push(ColumnClaim {
                                col: *col,
                                point: zeta_lo.to_vec(),
                                value: v,
                            });
                            v
                        });
                        b.mul_add(w, value, inner)
                    }
                    Coord::Sparse(_) => {
                        let weight = b.mul(eq_hi, w);
                        sparse.push(SparseShare {
                            side: s,
                            weight,
                            point: zeta_lo.to_vec(),
                        });
                        inner
                    }
                    Coord::Public(_) | Coord::Prod(..) | Coord::Sum(_) => {
                        unreachable!("no framework block of the RISC-V layout carries one")
                    }
                };
            }
            let leaf = b.add(beta, inner);
            acc = b.mul_add(eq_hi, leaf, acc);
        }
        // Every row of every block holds its leaf, the rest of the cube one.
        sel_terms.push(acc);
        sel_terms.push(values[s]);
        let sum = b.sum(&sel_terms);
        totals[s] = b.add_const(sum, F192::ONE);
    }
    Bus {
        claims,
        point,
        forms,
        producers,
        totals,
        sparse,
        alphas,
        weights,
        beta,
    }
}

/// A table's coordinate over its own columns.
fn local(c: &Coord, base: usize) -> Coord {
    match c {
        Coord::Col(i) => Coord::Col(i - base),
        Coord::Prod(i, j) => Coord::Prod(i - base, j - base),
        Coord::Sum(cs) => Coord::Sum(cs.iter().map(|c| local(c, base)).collect()),
        other => other.clone(),
    }
}

/// A coordinate at the table's claimed column values.
fn coord_value(b: &mut Builder, c: &Coord, values: &[Ew]) -> Ew {
    match c {
        Coord::Const(v) => b.e_const(F192::from(*v)),
        Coord::Col(i) => values[*i],
        Coord::Prod(i, j) => b.mul(values[*i], values[*j]),
        Coord::Sum(cs) => {
            let terms: Vec<Ew> = cs.iter().map(|c| coord_value(b, c, values)).collect();
            b.sum(&terms)
        }
        _ => unreachable!("a table's block carries no virtual coordinate"),
    }
}

/// `w·c(values) + acc`, a constant coordinate by one EXK row.
pub(crate) fn weighted_coord(b: &mut Builder, w: Ew, c: &Coord, values: &[Ew], acc: Ew) -> Ew {
    match c {
        Coord::Const(v) => b.mul_const_add(w, F192::from(*v), acc),
        Coord::Sum(cs) => cs.iter().fold(acc, |acc, c| weighted_coord(b, w, c, values, acc)),
        _ => {
            let x = coord_value(b, c, values);
            b.mul_add(w, x, acc)
        }
    }
}

/// `leaf::producer_affine_evals` at `chi`: each bit's public column short of the program's columns.
fn producer_affine_evals(b: &mut Builder, p: &Producer, w: &[Ew], beta: Ew, chi: &[Ew]) -> Vec<Ew> {
    let mut constant = beta;
    let mut affine: Vec<(Ew, Vec<u64>)> = Vec::new();
    for (c, &weight) in p.coords.iter().zip(w) {
        match c {
            Coord::Const(v) => constant = b.mul_const_add(weight, F192::from(*v), constant),
            Coord::IntIndex { base, shift } => {
                constant = b.mul_const_add(weight, F192::from(*base), constant);
                affine.push((weight, (0..p.kappa).map(|k| 1u64 << (k as u32 + shift)).collect()));
            }
            Coord::Public(_) => {}
            _ => unreachable!("a producer's tuple is public"),
        }
    }
    let mut evals = Vec::with_capacity(p.bits);
    for bit in 0..p.bits {
        let mut eval = constant;
        for (weight, monomials) in &affine {
            let mut s = b.zero();
            for (&z, &m) in chi.iter().zip(monomials) {
                s = b.mul_const_add(z, F192::from(primitives::field::F64(m)), s);
            }
            eval = b.mul_add(*weight, s, eval);
        }
        evals.push(b.add_const(eval, F192::ONE));
        if bit + 1 < p.bits {
            constant = b.square(constant);
            for (weight, monomials) in &mut affine {
                *weight = b.square(*weight);
                monomials
                    .iter_mut()
                    .for_each(|m| *m = (primitives::field::F64(*m) * primitives::field::F64(*m)).0);
            }
        }
    }
    evals
}

/// What the table sumcheck leaves (`constraints::Final` and the program claim it implies).
pub(super) struct TableSumcheck {
    /// Per air, its point and its sent columns' values.
    pub(super) claims: Vec<(Vec<Ew>, Vec<Ew>)>,
}

/// The announced sizes: every height and the rate are the shape's, the final clock a live, cycle-aligned
/// word (`Announcement::read`).
pub(super) fn read_announcement(
    b: &mut Builder,
    t: &mut Transcript,
    taus: &[usize; N_TABLES],
    log_inv_rate: usize,
) -> Ew {
    for &tau in taus {
        let x = t.next_scalar(b);
        b.eq_e_const(x, F192::new(tau as u64, 0, 0));
    }
    let x = t.next_scalar(b);
    b.eq_e_const(x, F192::new(log_inv_rate as u64, 0, 0));
    let ts = t.next_scalar(b);
    let [word, high, top] = b.e_to_k(ts);
    b.eq_k_const(high, 0);
    b.eq_k_const(top, 0);
    let bits = b.split(word);
    for (i, &bit) in bits.iter().enumerate() {
        let live = i == LIVE_BIT as usize;
        if live || i > LIVE_BIT as usize || i < CYCLE.trailing_zeros() as usize {
            b.eq_k_const(bit, u64::from(live));
        }
    }
    ts
}

/// `constraints::verify` on the RISC-V batch (`cpu::batch`), then `deferred::program_claim`.
pub(super) fn table_sumcheck(
    b: &mut Builder,
    t: &mut Transcript,
    l: &Layout,
    bus: &Bus,
) -> (TableSumcheck, ProgramClaim) {
    let xi = t.sample(b);
    let push = b.one();
    let pull = xi;
    let target = b.mul_add(xi, bus.totals[1], bus.totals[0]);
    let spans = &Schema::get().spans;

    let taus: Vec<usize> = l
        .taus
        .iter()
        .copied()
        .chain(l.producers.iter().map(|p| p.kappa))
        .collect();
    let n = taus.iter().copied().max().unwrap_or(0);
    let mut claim = target;
    let mut weights: Vec<Ew> = vec![b.one(); taus.len()];
    let mut chi: Vec<Option<Ew>> = vec![None; n];
    for j in 0..n {
        let m = n - 1 - j;
        let h = t.next_round_poly(b, 4, claim, None);
        let rk = t.sample(b);
        chi[m] = Some(rk);
        claim = poly_eval(b, &h, rk);
        let s = b.add(bus.point[m], rk);
        for (w, &tau) in weights.iter_mut().zip(&taus) {
            *w = if tau > m {
                times_one_plus(b, *w, s)
            } else {
                b.mul(*w, rk)
            };
        }
    }
    let chi: Vec<Ew> = chi
        .into_iter()
        .map(|c| c.expect("every round binds its variable"))
        .collect();

    let mut residual = claim;
    let mut claims = Vec::with_capacity(taus.len());
    for (table, &(_, n_cols)) in spans.iter().enumerate() {
        let values = t.next_scalars(b, n_cols);
        // `Σ_s power_s·Σ_blocks eq_hi·(β + Σ_i w_i·c_i)`.
        let mut summand = b.zero();
        for side in 0..2 {
            let mut form = b.zero();
            for block in bus.forms[table].iter().filter(|f| f.side == side) {
                let mut leaf = bus.beta;
                for (i, c) in block.coords.iter().enumerate() {
                    leaf = weighted_coord(b, bus.weights[i], c, &values, leaf);
                }
                form = b.mul_add(block.selector, leaf, form);
            }
            summand = b.mul_add(if side == 0 { push } else { pull }, form, summand);
        }
        residual = b.mul_add(weights[table], summand, residual);
        claims.push((chi[..l.taus[table]].to_vec(), values));
    }

    let [p] = &l.producers[..] else {
        unreachable!("one lookup array, the bytecode")
    };
    let point = chi[..p.kappa].to_vec();
    let bits = t.next_scalars(b, p.bits);
    let public = producer_affine_evals(b, p, &bus.weights, bus.beta, &point);
    let selectors = &bus.producers[0];
    let producer_weight = weights[N_TABLES];
    // `Σ_i c_i·(1 + b_i·P'_i)`, the push side's power being one.
    let mut summand = b.zero();
    for i in 0..p.bits {
        let one = b.one();
        let leaf = b.mul_add(bits[i], public[i], one);
        summand = b.mul_add(selectors[i], leaf, summand);
    }
    residual = b.mul_add(producer_weight, summand, residual);
    let twist: Vec<Ew> = (0..p.bits)
        .map(|i| {
            let wc = b.mul(producer_weight, selectors[i]);
            b.mul(wc, bits[i])
        })
        .collect();
    claims.push((point.clone(), bits));
    let target_weight = product(b, &chi);

    let [image] = &bus.sparse[..] else {
        unreachable!("RAM's image is the one sparse column")
    };
    let side_power = if image.side == 0 { push } else { pull };
    let tw = b.mul(target_weight, side_power);
    let image_weight = b.mul(tw, image.weight);
    let mut bytecode = point;
    bytecode.extend(&bus.alphas);
    (
        TableSumcheck { claims },
        ProgramClaim {
            bytecode,
            twist,
            image_weight,
            image_point: image.point.clone(),
            value: residual,
        },
    )
}

/// A column claim located in the stack (`Layout::slot_claim`).
fn slot_claim(l: &Layout, c: ColumnClaim) -> StackClaim {
    match l.placements[c.col] {
        Placement::Committed(window) => StackClaim::Point {
            offset: window.offset,
            low_point: c.point,
            value: c.value,
        },
        Placement::Port {
            offset,
            port,
            stride_log,
        } => StackClaim::Strided {
            offset,
            slot: port,
            stride_log,
            point: c.point,
            value: c.value,
        },
    }
}

/// `Layout::opening_claims`: the bus's framework claims, each table's columns, then the exit's.
pub(super) fn opening_claims(
    b: &mut Builder,
    l: &Layout,
    bus_claims: Vec<ColumnClaim>,
    tables: &TableSumcheck,
    output: &[Ew; 4],
) -> Vec<StackClaim> {
    let spans = &Schema::get().spans;
    let mut claims = bus_claims;
    for (&(base, _), (chi, evals)) in spans.iter().zip(&tables.claims) {
        claims.extend(evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
            col: base + c,
            point: chi.clone(),
            value,
        }));
    }
    let register_point = |b: &mut Builder, reg: Reg| -> Vec<Ew> {
        (0..RegisterFile::LOG_CELLS)
            .map(|bit| b.e_const(F192::new((reg.index() >> bit & 1) as u64, 0, 0)))
            .collect()
    };
    let point = register_point(b, Reg::SYSCALL);
    let value = b.e_const(F192::new(Syscall::Exit.number(), 0, 0));
    claims.push(ColumnClaim {
        col: Shared::RegFin.col(),
        point,
        value,
    });
    for (reg, &value) in Reg::OUTPUTS.into_iter().zip(output) {
        let point = register_point(b, reg);
        claims.push(ColumnClaim {
            col: Shared::RegFin.col(),
            point,
            value,
        });
    }
    claims.into_iter().map(|c| slot_claim(l, c)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::Program;
    use crate::pcs::Rate;
    use crate::rec::transcript::Source;
    use crate::rv::asm::*;

    /// A program with a loop, a store and a load, so that every framework block is read.
    pub(crate) fn small_program() -> Program {
        let text = Asm::new()
            .li(Reg::T0, 0x0123_4567_89ab_cdef)
            .li(Reg::T1, 9)
            .r(Xor, Reg::A0, Reg::T0, Reg::T1)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    }

    /// The circuit's bus and table sumcheck leave the native core's program claim.
    #[test]
    fn the_circuit_leaves_the_native_program_claim() {
        let program = small_program();
        let (proof, output, _) = program.prove(&[], Rate::MIN).expect("the run halts");
        let native = program.verify_core(&output, &proof).expect("an honest proof");
        let raw = program.verify_to_raw(&output, &proof).expect("an honest proof");
        let taus: [usize; N_TABLES] = std::array::from_fn(|i| proof.stream[i].c0 as usize);
        let build = |source: Source| {
            let mut b = Builder::new();
            let output = output.map(|o| b.free_k(o));
            let iv = b.d_const(program.fs_seed().map(|w| w.0));
            let first = b.k_to_e([output[0], output[1], output[2]]);
            let mut t = Transcript::new(&mut b, iv, (first, output[3]), source);
            let ts = read_announcement(&mut b, &mut t, &taus, 1);
            let l = Layout::new(program.rv(), taus, 0);
            t.next_root(&mut b);
            let bus = verify_balance(&mut b, &mut t, &l, ts);
            let (_, claim) = table_sumcheck(&mut b, &mut t, &l, &bus);
            (b, claim)
        };
        let (b, claim) = build(Source::Proof(&raw));
        let point = &native.program.terms[0].1;
        let values = |ws: &[Ew]| ws.iter().map(|&w| b.e(w)).collect::<Vec<_>>();
        assert_eq!(values(&claim.bytecode), point.bytecode);
        assert_eq!(values(&claim.twist), point.twist);
        assert_eq!(b.e(claim.image_weight), point.image_weight);
        assert_eq!(values(&claim.image_point), point.image_point);
        assert_eq!(b.e(claim.value), native.program.value);
        let (circuit, _, failures) = b.finish();
        assert!(failures.is_empty(), "{failures:?}");
        let (shape_circuit, _, _) = build(Source::Shape).0.finish();
        assert_eq!(circuit, shape_circuit);
    }
}
