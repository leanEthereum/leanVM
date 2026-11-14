//! `soundness-witness-tamper`: the prover edits its own witness after the honest run built it and before committing
//! it, then proves the edited witness as if it were honest (`cpu::tamper`). The edits are adversarial: one word, a
//! padding row, coordinated lies that keep every other flush consistent (a memory word and all its readers, an
//! operand and the result, a DEREF pointer and its cell), a read count zeroed with the chain renumbered around it so
//! only the count channel can object, swapped rows, the Keccak states.
//!
//! The judge is `WitnessView::check`, the relation the protocol is meant to enforce, evaluated directly on the edited
//! witness. A proof that verifies while that check fails is a hole in the protocol (Critical). A proof that verifies
//! for an edit made invalid by construction (a `SET` destination or a public-input cell changed) is Critical however
//! the check rules, since it would be a hole in the arithmetization. An edit the check accepts is a valid witness
//! (swapped rows, the stack's zero pad, an unused cell) and only noted.

use super::fixtures;
use crate::source::Rng;
use crate::{Ctx, Finding, Outcome, Source, catch};
use leanvm_core::cpu::tamper::{self, Access, Owner, WitnessView};
use leanvm_core::cpu::{KeccakLane, MEM_HI, MEM_LO, Stats, keccak_value, schema};
use primitives::field::{F64, F128};
use std::cell::RefCell;
use std::rc::Rc;

const XOR: usize = 0;
const MUL: usize = 1;
const SET: usize = 2;
const DEREF: usize = 3;
const JUMP: usize = 4;
const KECCAK: usize = 5;
/// `JUMP`'s condition, inverse hint and taken indicator, as local columns (`tables::jump`).
const JUMP_COND: usize = 5;
const JUMP_W: usize = 12;
const JUMP_B: usize = 13;
/// Lanes of a Keccak state, and the slots of `q_keccak` its input and its state after `DEPTH` rounds take.
const LANES: usize = 25;

/// What the edit did.
#[derive(Default)]
struct Report {
    /// The edit's kind and where: the finding key's tail.
    what: String,
    /// The edit changed something.
    applied: bool,
    /// Invalid whatever the reference check says: the program could not have produced it.
    invalid_by_construction: bool,
    /// The reference check on the edited witness.
    relation: Option<Result<(), String>>,
    /// The reference check on the honest witness, when run.
    honest: Option<Result<(), String>>,
}

const KINDS: &[(&str, u32)] = &[
    ("word", 6),
    ("padding-row", 2),
    ("set-destination-lie", 2),
    ("public-input-lie", 1),
    ("operand-and-result", 2),
    ("deref-pointer", 2),
    ("zero-count", 3),
    ("count-shift", 1),
    ("recount-swap", 1),
    ("swap-rows", 1),
    ("swap-rows-partial", 2),
    ("pad-tail", 1),
    ("keccak-state", 2),
    ("keccak-consistent-input", 2),
    ("jump-flip", 2),
    ("jump-inverse", 2),
];

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let kind = KINDS[src.weighted(&KINDS.iter().map(|k| k.1).collect::<Vec<_>>())].0;
    let fixture = match kind {
        "keccak-state" | "keccak-consistent-input" => {
            fixtures::pick_named(src, &["inline/all_tables", "inline/keccak_heavy"])
        }
        _ => fixtures::pick(src),
    };
    let rate = crate::programs::log_inv_rate(src);
    // Only a program whose honest proof verifies: an edit is judged against that.
    if fixtures::honest(fixture, rate)?.is_none() {
        return Ok(());
    }
    let precheck = src.chance(1, 8);
    let mut rng = src.rng();
    let report = Rc::new(RefCell::new(Report::default()));
    let sink = report.clone();
    tamper::arm(Box::new(move |view: &mut WitnessView| {
        let mut r = sink.borrow_mut();
        if precheck {
            r.honest = Some(view.check());
        }
        if let Some((what, invalid)) = edit(kind, view, &mut rng) {
            r.what = what;
            r.applied = true;
            r.invalid_by_construction = invalid;
            r.relation = Some(view.check());
        }
    }));
    let context = format!("soundness-witness-tamper {}", fixture.name);
    let proved = catch(|| leanvm_core::cpu::prove(&fixture.program, fixture.public_input, rate));
    tamper::disarm();
    let report = report.take();
    if let Some(Err(e)) = &report.honest {
        return Err(Finding::low(
            format!("soundness-witness-tamper: the reference check refuses an honest witness ({e})"),
            format!("program {}, rate {rate}", fixture.name),
        ));
    }
    if !report.applied {
        ctx.note(format!("{kind} not applicable"));
        return Ok(());
    }
    let relation = report.relation.clone().unwrap_or(Ok(()));
    if std::env::var_os("LEANVM_FUZZ_VERBOSE").is_some() {
        eprintln!("{}: {}, reference check {relation:?}", fixture.name, report.what);
    }
    ctx.note(format!(
        "{kind} {}",
        relation
            .as_ref()
            .map_or_else(|e| format!("breaks {e}"), |_| "keeps the relation".into())
    ));
    let proof = match proved {
        Err(_) => {
            // A tampered witness that panics the prover is never judged against the verifier, so
            // it cannot hide a hole by itself; but an assert that fires only on a MALICIOUS
            // witness (a prover-side consistency check not gated on `witness_is_honest`) would
            // silently blind this target from then on. Recorded as a Low so a campaign surfaces it.
            if relation.is_ok() {
                return Err(Finding::low(
                    format!("{kind}: a tampered witness panics the prover"),
                    format!("the reference check keeps the relation ({relation:?}); a prover-side assert fires only on tampering"),
                ));
            }
            ctx.note(format!("{kind} prover panicked"));
            return Ok(());
        }
        Ok(Err(e)) => {
            ctx.note(format!(
                "{kind} prover refused {}",
                crate::programs::prove_error_kind(&e)
            ));
            return Ok(());
        }
        Ok(Ok((proof, _))) => proof,
    };
    let verdict = super::verify_caught(fixture, &proof, &context)?;
    let detail = || {
        format!(
            "program {}, rate {rate}, edit {}, reference check {relation:?}",
            fixture.name, report.what
        )
    };
    match (&verdict, &relation) {
        (Ok(_), Err(broken)) => Err(Finding::critical(
            format!(
                "soundness-witness-tamper: a witness breaking `{}` verifies: {}",
                crate::findings::normalize(broken),
                key_of(&report.what)
            ),
            detail(),
        )),
        (Ok(_), Ok(())) if report.invalid_by_construction => Err(Finding::critical(
            format!(
                "soundness-witness-tamper: an invalid witness the relation misses verifies: {}",
                key_of(&report.what)
            ),
            detail(),
        )),
        (Ok(_), Ok(())) => {
            ctx.note(format!("{kind} benign, verifies"));
            Ok(())
        }
        (Err(e), Ok(())) => {
            ctx.note(format!(
                "{kind} keeps the relation, rejected {}",
                fixtures::error_name(e)
            ));
            Err(Finding::low(
                format!(
                    "soundness-witness-tamper: a witness the reference check accepts is rejected: {}",
                    key_of(&report.what)
                ),
                detail(),
            ))
        }
        (Err(e), Err(_)) => {
            ctx.note(format!("{kind} rejected {}", fixtures::error_name(e)));
            Ok(())
        }
    }
}

/// The part of an edit's description a finding is keyed by: its kind and column, no row or value.
fn key_of(what: &str) -> String {
    what.split(" @").next().unwrap_or(what).to_string()
}

fn nonzero(rng: &mut Rng) -> F64 {
    match rng.below(3) {
        0 => F64(1 << rng.below(64)),
        1 => F64(1),
        _ => F64(rng.next_u64().max(1)),
    }
}

fn pick<T: Clone>(rng: &mut Rng, items: &[T]) -> Option<T> {
    (!items.is_empty()).then(|| items[rng.below(items.len() as u64) as usize].clone())
}

/// Apply edit `kind`, returning its description and whether it is invalid by construction; `None` when the witness
/// offers it nothing to edit.
fn edit(kind: &str, view: &mut WitnessView, rng: &mut Rng) -> Option<(String, bool)> {
    match kind {
        "word" => word(view, rng, false),
        "padding-row" => word(view, rng, true),
        "set-destination-lie" => {
            let accesses = view.accesses();
            let sets: Vec<&Access> = accesses.iter().filter(|a| a.table == SET && a.cell.is_some()).collect();
            let a = pick(rng, &sets)?;
            let delta = word_delta(rng);
            let also_immediate = rng.below(2) == 0;
            shift_cell(view, &accesses, a.cell?, delta, (!also_immediate).then_some(SET));
            Some((
                format!(
                    "set-destination-lie{} @ cell {:?}",
                    if also_immediate { " with immediate" } else { "" },
                    a.cell
                ),
                true,
            ))
        }
        "public-input-lie" => {
            let accesses = view.accesses();
            let cell = rng.below(2) as usize;
            let delta = F128::new(nonzero(rng).0, 0);
            shift_cell(view, &accesses, cell, delta, None);
            Some((format!("public-input-lie @ cell {cell}"), true))
        }
        "operand-and-result" => {
            let accesses = view.accesses();
            let rows: Vec<&Access> = accesses
                .iter()
                .filter(|a| matches!(a.table, XOR | MUL) && a.values[0].is_some())
                .collect();
            let a = pick(rng, &rows)?;
            let row_accesses: Vec<&Access> = accesses
                .iter()
                .filter(|b| b.table == a.table && b.row == a.row)
                .collect();
            let result = row_accesses.iter().find(|b| b.values.iter().all(Option::is_none))?;
            let other = row_accesses
                .iter()
                .find(|b| b.values[0].is_some() && b.values[0] != a.values[0])?;
            let delta = word_delta(rng);
            let other_word = read_word(view, &other.values, other.row);
            add_word(view, &a.values, a.row, delta);
            // The result cell follows the edited operand: `+ delta` for XOR, `+ delta·b` for MUL.
            let result_delta = if a.table == XOR { delta } else { delta * other_word };
            if let Some(cell) = result.cell {
                shift_cell(view, &accesses, cell, result_delta, None);
            }
            let also_cell = rng.below(2) == 0;
            if also_cell && let Some(cell) = a.cell {
                // The operand's cell and its other readers too: the lie is then only in where the operand came from.
                shift_cell_except(view, &accesses, cell, delta, (a.table, a.row));
            }
            Some((
                format!(
                    "operand-and-result {}{} @ row {}",
                    Stats::TABLES[a.table],
                    if also_cell { " with cell" } else { "" },
                    a.row
                ),
                false,
            ))
        }
        "deref-pointer" => {
            let accesses = view.accesses();
            let pointers: Vec<&Access> = accesses
                .iter()
                .filter(|a| a.table == DEREF && a.values[1].is_none() && a.values[0].is_some())
                .collect();
            let a = pick(rng, &pointers)?;
            let p = a.values[0]?;
            let old = view.column(p)[a.row];
            let new = old * F64::G;
            view.column_mut(p)[a.row] = new;
            if rng.below(2) == 0
                && let Some(cell) = a.cell
            {
                shift_cell_except(view, &accesses, cell, F128::new((old + new).0, 0), (a.table, a.row));
            }
            Some((format!("deref-pointer @ row {}", a.row), false))
        }
        "zero-count" => zero_count(view, rng),
        "count-shift" => {
            if rng.below(2) == 0 {
                let accesses = view.accesses();
                let a = pick(rng, &accesses)?;
                let cell = a.cell?;
                let c = &mut view.column_mut(tamper::MFCNT)[cell];
                *c *= F64::G;
                Some(("count-shift MFCNT".into(), false))
            } else {
                let counts = view.column(tamper::BFCNT);
                let executed: Vec<usize> = (0..counts.len()).filter(|&pc| counts[pc] != F64::ONE).collect();
                let pc = pick(rng, &executed)?;
                view.column_mut(tamper::BFCNT)[pc] *= F64::G;
                Some(("count-shift BFCNT".into(), false))
            }
        }
        "recount-swap" => {
            let accesses = view.accesses();
            let a = pick(rng, &accesses)?;
            let peers: Vec<&Access> = accesses
                .iter()
                .filter(|b| {
                    b.cell == a.cell && b.count.is_some() && (b.table, b.row, b.count) != (a.table, a.row, a.count)
                })
                .collect();
            let b = pick(rng, &peers)?;
            let (ca, cb) = (a.count?, b.count?);
            let (va, vb) = (view.column(ca)[a.row], view.column(cb)[b.row]);
            view.column_mut(ca)[a.row] = vb;
            view.column_mut(cb)[b.row] = va;
            Some(("recount-swap".into(), false))
        }
        "swap-rows" | "swap-rows-partial" => {
            let partial = kind == "swap-rows-partial";
            let t = rng.below(6) as usize;
            let rows = view.layout.rows[t];
            if rows < 2 {
                return None;
            }
            let (r1, r2) = (rng.below(rows as u64) as usize, rng.below(rows as u64) as usize);
            if r1 == r2 {
                return None;
            }
            let base = schema().base[t];
            let n = leanvm_core::tables::tables()[t].n_committed_columns();
            let skip = partial.then(|| base + rng.below(n as u64) as usize);
            for c in base..base + n {
                if Some(c) == skip {
                    continue;
                }
                let col = view.column_mut(c);
                if col.len() > r1.max(r2) {
                    col.swap(r1, r2);
                }
            }
            if t == KECCAK && skip.is_none() {
                let steps = 1 << view.layout.taus[KECCAK];
                let states = view.keccak_states_mut();
                for slot in LANES..states.len() / steps {
                    states.swap(slot * steps + r1, slot * steps + r2);
                }
            }
            let skipped = skip.map_or(String::new(), |c| format!(" but {}", view.name(c)));
            Some((format!("{kind} {}{skipped}", Stats::TABLES[t]), false))
        }
        "pad-tail" => {
            let placed = view.placed_len();
            let stack = view.stack_mut();
            if placed >= stack.len() {
                return None;
            }
            let i = placed + rng.below((stack.len() - placed) as u64) as usize;
            stack[i] += nonzero(rng);
            Some(("pad-tail".into(), false))
        }
        "keccak-state" => {
            let steps = 1 << view.layout.taus[KECCAK];
            let real = view.layout.rows[KECCAK];
            let states = view.keccak_states_mut();
            let slots = states.len() / steps;
            let slot = rng.below(slots as u64) as usize;
            let step = if real > 0 && rng.below(4) != 0 {
                rng.below(real as u64)
            } else {
                rng.below(steps as u64)
            } as usize;
            states[slot * steps + step] += nonzero(rng);
            let part = if slot < LANES { "input" } else { "state" };
            Some((format!("keccak-state {part} @ slot {slot} step {step}"), false))
        }
        "keccak-consistent-input" => {
            let steps = 1 << view.layout.taus[KECCAK];
            let real = view.layout.rows[KECCAK];
            if real == 0 {
                return None;
            }
            let step = rng.below(real as u64) as usize;
            let lane = rng.below(LANES as u64) as usize;
            let delta = nonzero(rng);
            let states = view.keccak_states_mut();
            states[lane * steps + step] += delta;
            let inputs: Vec<[u64; LANES]> = (0..steps)
                .map(|j| std::array::from_fn(|l| states[l * steps + j].0))
                .collect();
            let shape = keccak_gkr::Shape::new(steps, leanvm_core::keccak::DEPTH);
            drop(keccak_gkr::Witness::generate(shape, &inputs, states));
            let mut output = inputs[step];
            primitives::hash::keccak_f(&mut output);
            let base = schema().base[KECCAK];
            for c in base..base + leanvm_core::tables::tables()[KECCAK].n_committed_columns() {
                if let Some(KeccakLane::Output(l)) = keccak_value(c) {
                    view.column_mut(c)[step] = F64(output[l]);
                }
            }
            Some(("keccak-consistent-input".into(), false))
        }
        "jump-flip" => {
            let real = view.layout.rows[JUMP];
            if real == 0 {
                return None;
            }
            let row = rng.below(real as u64) as usize;
            let base = schema().base[JUMP];
            let cond = view.column(base + JUMP_COND)[row];
            let b = view.column(base + JUMP_B)[row];
            let flipped = if b == F64::ZERO { F64::ONE } else { F64::ZERO };
            view.column_mut(base + JUMP_B)[row] = flipped;
            if rng.below(2) == 0 {
                // The inverse hint follows, so only the branch's own identity can object.
                let w = if flipped == F64::ONE && cond != F64::ZERO {
                    cond.inv()
                } else {
                    F64::ZERO
                };
                view.column_mut(base + JUMP_W)[row] = w;
            }
            Some(("jump-flip".into(), false))
        }
        "jump-inverse" => {
            // The inverse hint of a taken branch, which no flush carries: only `b = cond·w` pins it.
            let real = view.layout.rows[JUMP];
            let base = schema().base[JUMP];
            let taken: Vec<usize> = (0..real)
                .filter(|&r| view.column(base + JUMP_COND)[r] != F64::ZERO)
                .collect();
            let row = pick(rng, &taken)?;
            view.column_mut(base + JUMP_W)[row] += nonzero(rng);
            Some(("jump-inverse".into(), false))
        }
        _ => unreachable!("an edit without a case: {kind}"),
    }
}

/// One word of one column: a real row, or with `padding` a padding row of a table column.
fn word(view: &mut WitnessView, rng: &mut Rng, padding: bool) -> Option<(String, bool)> {
    let n = view.n_columns();
    let candidates: Vec<usize> = (0..n)
        .filter(|&c| {
            let len = view.column(c).len();
            match (padding, view.real_rows(c)) {
                (_, _) if len == 0 => false,
                (true, Some(real)) => real < len,
                (true, None) => false,
                (false, Some(real)) => real > 0,
                (false, None) => true,
            }
        })
        .collect();
    let shared: Vec<usize> = candidates
        .iter()
        .copied()
        .filter(|&c| view.owner(c) == Owner::Shared)
        .collect();
    let c = if !padding && rng.below(3) == 0 {
        pick(rng, &shared)?
    } else {
        pick(rng, &candidates)?
    };
    let len = view.column(c).len();
    let row = match view.real_rows(c) {
        Some(real) if padding => real + rng.below((len - real) as u64) as usize,
        Some(real) => rng.below(real as u64) as usize,
        None => {
            // A cell (or pc) the run touched, mostly: an untouched cell is free.
            let counts = view.column(if c == tamper::BFCNT {
                tamper::BFCNT
            } else {
                tamper::MFCNT
            });
            let touched: Vec<usize> = (0..counts.len().min(len)).filter(|&i| counts[i] != F64::ONE).collect();
            match pick(rng, &touched) {
                Some(i) if rng.below(4) != 0 && c != leanvm_core::cpu::QKECCAK => i,
                _ => rng.below(len as u64) as usize,
            }
        }
    };
    view.column_mut(c)[row] += nonzero(rng);
    let kind = if padding { "padding-row" } else { "word" };
    Some((format!("{kind} {} @ row {row}", view.name(c)), false))
}

/// A nonzero change of a machine word: mostly its low limb, sometimes the others.
fn word_delta(rng: &mut Rng) -> F128 {
    match rng.below(4) {
        0 => F128::new(0, nonzero(rng).0),
        1 => F128::new(rng.next_u64(), rng.next_u64().max(1)),
        _ => F128::new(nonzero(rng).0, 0),
    }
}

fn read_word(view: &WitnessView, values: &[Option<usize>; 2], row: usize) -> F128 {
    let limb = |c: Option<usize>| c.map_or(0, |c| view.column(c)[row].0);
    F128::new(limb(values[0]), limb(values[1]))
}

fn add_word(view: &mut WitnessView, values: &[Option<usize>; 2], row: usize, delta: F128) {
    for (c, d) in values.iter().zip(delta.to_limbs()) {
        if let Some(c) = c {
            view.column_mut(*c)[row] += F64(d);
        }
    }
}

/// Add `delta` to memory cell `cell` and to every read of it a column carries, leaving out the reads of table
/// `keep` (whose values a public column pins).
fn shift_cell(view: &mut WitnessView, accesses: &[Access], cell: usize, delta: F128, keep: Option<usize>) {
    for (c, d) in [MEM_LO, MEM_HI].into_iter().zip(delta.to_limbs()) {
        view.column_mut(c)[cell] += F64(d);
    }
    for a in accesses
        .iter()
        .filter(|a| a.cell == Some(cell) && Some(a.table) != keep)
    {
        add_word(view, &a.values, a.row, delta);
    }
}

fn shift_cell_except(view: &mut WitnessView, accesses: &[Access], cell: usize, delta: F128, skip: (usize, usize)) {
    for (c, d) in [MEM_LO, MEM_HI].into_iter().zip(delta.to_limbs()) {
        view.column_mut(c)[cell] += F64(d);
    }
    for a in accesses
        .iter()
        .filter(|a| a.cell == Some(cell) && (a.table, a.row) != skip)
    {
        add_word(view, &a.values, a.row, delta);
    }
}

/// Zero one read's count and change the word it reads. Its pull and push then carry `0` and `g·0 = 0` and cancel,
/// touching no cell; renumbering the cell's later reads and its final count closes the chain around it, so the bus
/// balances and only the count channel's nonzero product can object.
fn zero_count(view: &mut WitnessView, rng: &mut Rng) -> Option<(String, bool)> {
    let accesses = view.accesses();
    let readable: Vec<&Access> = accesses
        .iter()
        .filter(|a| a.count.is_some() && a.cell.is_some())
        .collect();
    let a = pick(rng, &readable)?;
    let cell = a.cell?;
    let count = |b: &Access| view.column(b.count.unwrap())[b.row];
    let mut chain: Vec<&Access> = vec![a];
    loop {
        let next = count(chain[chain.len() - 1]) * F64::G;
        match accesses
            .iter()
            .find(|b| b.cell == Some(cell) && b.count.is_some() && count(b) == next)
        {
            Some(b) if chain.len() < accesses.len() => chain.push(b),
            _ => break,
        }
    }
    let olds: Vec<F64> = chain.iter().map(|b| count(b)).collect();
    for (b, &previous) in chain[1..].iter().zip(&olds) {
        view.column_mut(b.count.unwrap())[b.row] = previous;
    }
    view.column_mut(tamper::MFCNT)[cell] = olds[olds.len() - 1];
    view.column_mut(a.count.unwrap())[a.row] = F64::ZERO;
    // The zeroed read then lies about its word where nothing else in the witness depends on it, so the bus still
    // balances and only the zero count betrays the lie: an operand whose result cell nothing else reads (the result
    // follows the lie), the target or frame of a branch not taken, or a taken branch's condition (its inverse
    // following).
    let mut lied = "";
    if rng.below(4) != 0 {
        let row: Vec<&Access> = accesses
            .iter()
            .filter(|b| b.table == a.table && b.row == a.row)
            .collect();
        match a.table {
            XOR | MUL if a.values[0].is_some() => {
                let other = row.iter().find(|b| b.values[0].is_some() && b.values[0] != a.values[0]);
                let result = row.iter().find(|b| b.values.iter().all(Option::is_none));
                if let (Some(other), Some(result)) = (other, result)
                    && let Some(c) = result.cell
                    && accesses.iter().filter(|b| b.cell == Some(c)).count() == 1
                    && result.cell != a.cell
                    && result.cell != other.cell
                {
                    let delta = word_delta(rng);
                    let other_word = read_word(view, &other.values, other.row);
                    add_word(view, &a.values, a.row, delta);
                    let follows = if a.table == XOR { delta } else { delta * other_word };
                    for (col, d) in [MEM_LO, MEM_HI].into_iter().zip(follows.to_limbs()) {
                        view.column_mut(col)[c] += F64(d);
                    }
                    lied = " with an operand lie";
                }
            }
            JUMP => {
                let base = schema().base[JUMP];
                let taken = view.column(base + JUMP_B)[a.row] != F64::ZERO;
                let v = a.values[0].unwrap_or(usize::MAX);
                if !taken && (v == base + JUMP_COND + 1 || v == base + JUMP_COND + 2) {
                    view.column_mut(v)[a.row] += nonzero(rng);
                    lied = " with a branch-target lie";
                } else if taken && v == base + JUMP_COND {
                    let cond = view.column(v)[a.row] * F64::G;
                    view.column_mut(v)[a.row] = cond;
                    view.column_mut(base + JUMP_W)[a.row] = cond.inv();
                    lied = " with a condition lie";
                }
            }
            _ => {}
        }
    }
    Some((
        format!("zero-count {}{lied} @ row {}", Stats::TABLES[a.table], a.row),
        false,
    ))
}
