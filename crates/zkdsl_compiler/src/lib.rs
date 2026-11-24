//! A compiler from a Python-like zkDSL (see `zkDSL.md`) to the ISA ([`isa::Op`]).
//! Produces a [`CompiledProgram`]: bytecode plus the prover's allocation hints, which `isa::Program::from` prepares for either prover.
//!
//! ## Calling convention
//!
//! A frame is fp-relative; operand `gᵏ` names cell `m[fp·gᵏ]`. Layout:
//!
//! | offset | contents |
//! |--------|----------|
//! | 0      | `retpc`, the return program counter |
//! | 1      | `retfp`, the caller frame pointer |
//! | 2 .. 2+nargs            | arguments |
//! | 2+nargs .. 2+nargs+nretcells | flattened return cells |
//! | rest                    | locals / temporaries / frame-pointer hints |
//!
//! A scalar or `HeapBuf` pointer occupies one return cell. A returned
//! `StackBuf(n)` occupies `n` consecutive cells and is copied into a consecutive
//! run in the caller; source-level tuple arity therefore differs from physical
//! return-cell count when a tuple contains a stack buffer.
//!
//! A **call** is `DEREF`-then-`JUMP`: the callee frame pointer is a fresh
//! prover-hinted cell; the args and `retfp` are stored with `DEREF`(`Cell`/`Fp`),
//! then `DEREF`(`Pc`) stores the return address `g²·pc` (the resume point after the
//! call `JUMP`). The callee returns with one `JUMP[one, 0, 1]`. A **`mul_range`
//! loop** lowers to a recursive helper that tests `i == g^hi` and, while not done,
//! runs the body and recurses on `i·g`.

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;

use field::{Base, Consts, F64, F128, as_base, g_pow};
use isa::pretty_integer;
use isa::{BitsDest, CompiledProgram, DerefMode, Op, OutCells, RHint};

mod ast;
mod field;
mod ir;
mod lower;
mod opt;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{f128_literal, parse, parse_const, parse_with_constants, parse_with_replacements};

/// Compile an [`Ast`] to a provable [`CompiledProgram`]. Panics on a malformed program
/// (unbound variable, missing `main`, address overflow).
pub fn compile(ast: &Ast) -> CompiledProgram {
    let (mut lowered, mut tables) = lower_all(ast);
    opt::optimize(&mut lowered, &mut tables);
    assemble(lowered, tables)
}

/// Lower every function, `main` first.
fn lower_all(ast: &Ast) -> (Vec<Lowered>, JumpTables) {
    // Lower main first (it follows the table writes at pc 0), then the rest, expanding loop helpers.
    let mut queue: Vec<Func> = Vec::new();
    let main = ast
        .funcs
        .iter()
        .find(|f| f.name == "main")
        .expect("program needs a `main`");
    assert!(!main.has_const_params(), "main cannot take Const parameters");
    assert!(!main.inline, "main cannot be `@inline`");
    queue.push(main.clone());
    for f in &ast.funcs {
        if f.name != "main" {
            queue.push(f.clone());
        }
    }
    // Definitions by name, for Const-parameter specialization at call sites.
    let defs: HashMap<&str, &Func> = ast.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    // Constant arrays by name, resolved at lowering (`NAME[i]`, `len(NAME)`).
    let const_arrays: HashMap<&str, &[F128]> = ast
        .const_arrays
        .iter()
        .map(|(name, values)| (name.as_str(), values.as_slice()))
        .collect();

    let mut loop_bounds = HashMap::new();
    let mut lowered: Vec<Lowered> = Vec::new();
    let mut tables = JumpTables::default();
    let mut i = 0;
    while i < queue.len() {
        let f = &queue[i];
        i += 1;
        // A function with Const parameters is a template (only its call-site
        // specializations are lowered); an `@inline` function is expanded at
        // each call site ([`FnLower::try_inline`]), never lowered standalone.
        if f.has_const_params() || f.inline {
            continue;
        }
        let f = f.clone();
        lowered.push(lower_func(
            &f,
            &mut queue,
            &defs,
            &const_arrays,
            &mut loop_bounds,
            &mut tables,
        ));
    }
    (lowered, tables)
}

/// Lay out the lowered functions and the jump tables, and resolve them to a [`CompiledProgram`].
fn assemble(mut lowered: Vec<Lowered>, mut tables: JumpTables) -> CompiledProgram {
    // The tables sit past `main`'s own cells. At pc 0, in `main`'s frame (`fp = g^0`),
    // one `SET` per slot not deferred writes them, then falls through into `main`.
    let tables_base = lowered[0].frame_size;
    let at_start = defer_tables(&mut lowered, &mut tables, tables_base);
    if !tables.slots.is_empty() {
        lowered[0].frame_size += tables.slots.len() as u32;
        let code: Vec<LInstr> = (tables.slots.iter().zip(tables_base..).zip(&at_start))
            .filter(|(_, start)| **start)
            .map(|((k, o), _)| LInstr {
                op: LOp::Set { o, k: k.clone() },
                line: 0,
                hints: Vec::new(),
            })
            .collect();
        let frame_size = lowered[0].frame_size;
        lowered.insert(
            0,
            Lowered {
                name: "__jump_tables".into(),
                code,
                frame_size,
                keep: frame_size,
                rets: 0..0,
                fixed: true,
            },
        );
    }
    if std::env::var("DBG_LOWER").is_ok() {
        for low in &lowered {
            eprintln!("== fn {} (frame {}) ==", low.name, pretty_integer(low.frame_size));
            for (i, ins) in low.code.iter().enumerate() {
                let index = pretty_integer(i);
                eprintln!("  {index:>5}: {:?}", ins.op);
            }
        }
    }
    // Assign entry program counters and frame sizes.
    let mut entry = HashMap::new();
    let mut frame_size = HashMap::new();
    let mut pc = 0u32;
    for l in &lowered {
        entry.insert(l.name.clone(), pc);
        frame_size.insert(l.name.clone(), l.frame_size);
        pc += l.code.len() as u32;
    }
    // The padded bytecode size `B` is fixed by the lowered length, so the halt
    // sentinel pc `g^{B-1}` (last slot) is known before resolving: `main`'s
    // `EndSentinel` jump dest resolves to it, and the program halts there in main's frame.
    let total: usize = lowered.iter().map(|l| l.code.len()).sum();
    // The sentinel needs a slot of its own PAST all real code: pad from
    // total + 1, so a program of exactly 2^k instructions doesn't collide
    // its last instruction with the halt pc.
    let bytecode_size = (total + 1).next_power_of_two();
    let sentinel = (bytecode_size - 1) as u32;

    // Resolve to bytecode + a hint map keyed by global pc.
    let mut prog: Vec<Op> = Vec::new();
    // Source line per pc, so a run-time failure can name a line instead of a pc.
    let mut src_lines: Vec<u32> = Vec::new();
    let mut hints: HashMap<u32, Vec<RHint>> = HashMap::new();
    for l in &mut lowered {
        let pc0 = entry[&l.name];
        for ins in &mut l.code {
            let here = prog.len() as u32;
            if !ins.hints.is_empty() {
                let rhs = ins
                    .hints
                    .drain(..)
                    .map(|h| match h {
                        Hint::NextFrameAddress => RHint::FrameAddress { offset: l.frame_size },
                        Hint::AllocLoopFrames {
                            ptr,
                            callee,
                            count,
                            tail,
                        } => {
                            let size = frame_size[&callee];
                            match count {
                                LoopCount::Constant(n) => RHint::Alloc {
                                    ptr,
                                    size: u32::try_from(n - 1)
                                        .ok()
                                        .and_then(|n| size.checked_mul(n))
                                        .and_then(|frames| frames.checked_add(tail))
                                        .expect("loop frames overflow"),
                                },
                                LoopCount::Bound { cell, start } => RHint::AllocFrames {
                                    ptr,
                                    size,
                                    end: cell,
                                    start_inverse: F64::G.pow(u128::from(start)).inv(),
                                    tail,
                                },
                            }
                        }
                        Hint::AllocFrame { ptr, callee } => RHint::Alloc {
                            ptr,
                            size: frame_size[&callee],
                        },
                        Hint::AllocArm { ptr, sel, callees } => RHint::AllocArm {
                            ptr,
                            sel,
                            sizes: callees.iter().map(|c| frame_size[c]).collect(),
                        },
                        Hint::AllocBuffer { ptr, size } => RHint::Alloc { ptr, size },
                        Hint::AllocBufferDyn { ptr, size } => RHint::AllocDyn { ptr, size },
                        Hint::Resolved(r) => r,
                    })
                    .collect();
                hints.insert(here, rhs);
            }
            src_lines.push(ins.line);
            prog.push(resolve(&ins.op, &entry, sentinel, pc0, l.frame_size, tables_base));
        }
    }

    // Pad the bytecode to `B` (the sentinel slot g^{B-1} must exist for execution).
    prog.resize(bytecode_size, Op::Set { o: 0, k: F128::ZERO });
    CompiledProgram {
        prog,
        hints,
        main_frame: frame_size["main"],
        fn_ranges: lowered
            .iter()
            .map(|l| (l.name.clone(), entry[&l.name], l.code.len() as u32))
            .collect(),
        src_lines,
    }
}

/// The jump-table slots that only code reached through one of `main`'s runtime-bounded loops
/// reads move from pc 0 into that loop's [`LOp::DeferWrite`], and `main`'s placeholders expand
/// (or go, for a loop no slot moved to). Which slots stay at pc 0.
fn defer_tables(lowered: &mut [Lowered], tables: &mut JumpTables, tables_base: u32) -> Vec<bool> {
    let moved = deferred_slots(lowered, tables);
    let mut at_start = vec![true; tables.slots.len()];
    for &s in moved.values().flatten() {
        at_start[s] = false;
    }
    expand_deferred(&mut lowered[0], tables, tables_base, &moved);
    at_start
}

/// The slots each of `main`'s runtime-bounded loops can write on its entry test, by loop.
///
/// A function runs only once control enters it: through the `SET` of its entry in a function
/// that calls it, or through a jump-table slot naming it, which a function reading that table
/// jumps to. Loop `lp` qualifies when only `main`, at its one call, and `lp` itself name it;
/// the functions only `lp` reaches are then the least set holding `lp` and every function all
/// of whose other callers it holds, and a table only they read is read only after `main` passed the
/// loop's entry test. `DeferEnter` runs the writes on that same test, just before the call.
fn deferred_slots(lowered: &[Lowered], tables: &JumpTables) -> HashMap<String, Vec<usize>> {
    let n_slots = tables.slots.len();
    let mut moved = HashMap::new();
    let loops: Vec<String> = (lowered[0].code.iter())
        .filter_map(|ins| match &ins.op {
            LOp::DeferEnter { lp, .. } => Some(lp.clone()),
            _ => None,
        })
        .collect();
    if loops.is_empty() {
        return moved;
    }
    let index: HashMap<&str, usize> = lowered.iter().enumerate().map(|(i, l)| (l.name.as_str(), i)).collect();
    // Each table starts at the slot a `Slot` names and runs to the next one.
    let mut starts: Vec<usize> = (lowered.iter().flat_map(|l| &l.code))
        .filter_map(|ins| match ins.op {
            LOp::Slot { first, .. } => Some(first as usize),
            _ => None,
        })
        .collect();
    starts.sort_unstable();
    starts.dedup();
    let table_of = |slot: usize| starts.partition_point(|&f| f <= slot).checked_sub(1);
    let mut readers = vec![std::collections::BTreeSet::new(); starts.len()];
    let mut callers = vec![std::collections::BTreeSet::new(); lowered.len()];
    let named = |k: &KVal| match k {
        KVal::Entry(c) | KVal::At(c, _) => index.get(c.as_str()).copied(),
        _ => None,
    };
    for (g, l) in lowered.iter().enumerate() {
        for ins in &l.code {
            match &ins.op {
                LOp::Set { k, .. } => {
                    if let Some(c) = named(k) {
                        callers[c].insert(g);
                    }
                }
                LOp::Slot { first, .. } => {
                    readers[table_of(*first as usize).unwrap()].insert(g);
                }
                _ => {}
            }
        }
    }
    for (slot, k) in tables.slots.iter().enumerate() {
        if let (Some(c), Some(t)) = (named(k), table_of(slot)) {
            callers[c].extend(readers[t].iter().copied());
        } else if let Some(c) = named(k) {
            // A slot no table holds: count it as named from everywhere.
            callers[c].extend(0..lowered.len());
        }
    }
    let main = &lowered[0].code;
    for lp in &loops {
        let l = index[lp.as_str()];
        // `main` names `lp` once, in the call whose `JUMP` tests the `DeferEnter`'s condition, and only `lp`'s own
        // tables do.
        let entry_sets: Vec<(usize, Off)> = (main.iter().enumerate())
            .filter_map(|(i, ins)| match &ins.op {
                LOp::Set { o, k: KVal::Entry(c) } if c == lp => Some((i, *o)),
                _ => None,
            })
            .collect();
        let enter = main
            .iter()
            .position(|ins| matches!(&ins.op, LOp::DeferEnter { lp: p, .. } if p == lp));
        let guarded = match (enter, entry_sets.as_slice()) {
            (Some(e), &[(i, cell)]) => {
                let LOp::DeferEnter { x, .. } = main[e].op else {
                    unreachable!()
                };
                e < i
                    && (main[i..].iter()).find_map(|ins| match ins.op {
                        LOp::Jump { oc, od, .. } if od == cell => Some(oc == x),
                        _ => None,
                    }) == Some(true)
            }
            _ => false,
        };
        let in_table = (tables.slots.iter().enumerate())
            .any(|(s, k)| named(k) == Some(l) && table_of(s).is_none_or(|t| readers[t].iter().any(|&r| r != l)));
        if !guarded || in_table || callers[l].iter().any(|&c| c != 0 && c != l) {
            continue;
        }
        let mut only = std::collections::BTreeSet::from([l]);
        loop {
            let before = only.len();
            for f in 1..lowered.len() {
                // A function's own references (a `match` table's arms, a loop's next iteration) need it entered first.
                let mut from = callers[f].iter().filter(|&&c| c != f).peekable();
                if from.peek().is_some() && from.all(|c| only.contains(c)) {
                    only.insert(f);
                }
            }
            if only.len() == before {
                break;
            }
        }
        let slots: Vec<usize> = (0..n_slots)
            .filter(|&s| table_of(s).is_some_and(|t| !readers[t].is_empty() && readers[t].is_subset(&only)))
            .collect();
        if !slots.is_empty() {
            moved.insert(lp.clone(), slots);
        }
    }
    moved
}

/// `main`'s placeholders expanded, its other jump targets moved with them.
fn expand_deferred(main: &mut Lowered, tables: &mut JumpTables, tables_base: u32, moved: &HashMap<String, Vec<usize>>) {
    let len = |op: &LOp| match op {
        LOp::DeferEnter { lp, .. } => moved.get(lp).map_or(0, |_| 3),
        LOp::DeferWrite { lp, .. } => moved.get(lp).map_or(0, |s| s.len() + 1),
        _ => 1,
    };
    let mut new_index = Vec::with_capacity(main.code.len() + 1);
    let mut at = 0u32;
    for ins in &main.code {
        new_index.push(at);
        at += len(&ins.op) as u32;
    }
    new_index.push(at);
    let write_at: HashMap<&str, u32> = (main.code.iter().enumerate())
        .filter_map(|(i, ins)| match &ins.op {
            LOp::DeferWrite { lp, .. } => Some((lp.as_str(), new_index[i])),
            _ => None,
        })
        .collect();
    let mut code = Vec::with_capacity(at as usize);
    let mut carried: Vec<Hint> = Vec::new();
    for (i, ins) in main.code.iter().enumerate() {
        let LInstr { op, line, hints } = ins.clone();
        carried.extend(hints);
        let ops = match op {
            LOp::DeferEnter { lp, x, t, r, one } if moved.contains_key(&lp) => vec![
                LOp::Set {
                    o: t,
                    k: KVal::Local(write_at[lp.as_str()]),
                },
                LOp::Set {
                    o: r,
                    k: KVal::Local(new_index[i] + 3),
                },
                LOp::Jump { oc: x, od: t, of: one },
            ],
            LOp::DeferWrite { lp, r, one } => {
                let slots = moved.get(&lp).map_or(&[][..], Vec::as_slice);
                let mut ops: Vec<LOp> = (slots.iter())
                    .map(|&s| LOp::Set {
                        o: tables_base + s as u32,
                        k: tables.slots[s].clone(),
                    })
                    .collect();
                if !slots.is_empty() {
                    ops.push(LOp::Jump {
                        oc: one,
                        od: r,
                        of: one,
                    });
                }
                ops
            }
            LOp::DeferEnter { .. } => vec![],
            LOp::Set { o, k: KVal::Local(t) } => vec![LOp::Set {
                o,
                k: KVal::Local(new_index[t as usize]),
            }],
            op => vec![op],
        };
        for op in ops {
            code.push(LInstr {
                op,
                line,
                hints: std::mem::take(&mut carried),
            });
        }
    }
    assert!(carried.is_empty(), "a hint on `main`'s last placeholder");
    main.code = code;
    for k in &mut tables.slots {
        if let KVal::At(n, i) = k
            && n == "main"
        {
            *i = new_index[*i as usize];
        }
    }
}

/// Render compiled bytecode as a human-readable disassembly. `fp[k]` is the cell
/// `m[fp·gᵏ]` (frame offset `k`); `*(p·gᵝ)` is the dereferenced cell. `SET`
/// constants that are small g-powers (code addresses, indices) show as `gʲ`.
pub fn disassemble(prog: &[Op]) -> String {
    // Reverse index for small g-powers, to pretty-print code addresses/indices.
    let mut gmap: HashMap<F64, usize> = HashMap::new();
    let mut acc = F64::ONE;
    for j in 0..(prog.len() + 512) {
        gmap.entry(acc).or_insert(j);
        acc = acc * F64::G;
    }
    // A machine word is 128-bit; K-valued immediates (high limb zero) may be small
    // g-powers (code addresses, indices), shown as `gʲ`.
    let kfmt = |k: F128| match as_base(k) {
        Some(lo) => match gmap.get(&lo) {
            Some(j) => format!("g^{j}"),
            None => format!("0x{:016x}", lo.0),
        },
        None => format!("0x{:016x}{:016x}", k.c1, k.c0),
    };

    let mut out = String::new();
    for (pc, op) in prog.iter().enumerate() {
        let line = match op {
            Op::Set { o, k } => format!("SET    fp[{o}] = {}", kfmt(*k)),
            Op::Xor { a, b, c } => format!("XOR    fp[{c}] = fp[{a}] ^ fp[{b}]"),
            Op::Mul { a, b, c } => format!("MUL    fp[{c}] = fp[{a}] * fp[{b}]"),
            Op::Deref { o1, o2, o3, mode } => {
                let src = match mode {
                    DerefMode::Cell => format!("fp[{o3}]"),
                    DerefMode::Pc => "g²·pc".to_string(),
                    DerefMode::Fp => "fp".to_string(),
                };
                format!("DEREF  *(fp[{o1}]·g^{o2}) = {src}  [{mode:?}]")
            }
            Op::Jump { oc, od, of } => {
                format!("JUMP   if fp[{oc}]≠0: pc=fp[{od}], fp=fp[{of}]")
            }
            Op::Keccak {
                m,
                tail,
                b8,
                cap,
                out,
                in_odd,
                out_odd,
                out_cells,
            } => {
                let layout = |odd: bool| if odd { "odd" } else { "even" };
                format!(
                    "KECCAK fp[{out}..+{}] {} = keccak_f(fp[{}],fp[{}],fp[{}],fp[{}], tail=fp[{tail}..+4], b8=fp[{b8}], cap=fp[{cap}..+4]) {}",
                    out_cells.cells(),
                    layout(*out_odd),
                    m[0],
                    m[1],
                    m[2],
                    m[3],
                    layout(*in_odd)
                )
            }
        };
        writeln!(out, "{:>6}  {line}", pretty_integer(pc)).unwrap();
    }
    out
}

fn resolve(op: &LOp, entry: &HashMap<String, u32>, sentinel: u32, pc0: u32, frame_size: u32, tables: u32) -> Op {
    let resolve_kval = |kv: &KVal| -> F128 {
        match kv {
            KVal::FrameSize => g_pow(frame_size as usize).into(),
            KVal::Const(c) => *c,
            // Address / entry / sentinel constants are K-valued g-powers;
            // embed them canonically as (c0, 0).
            KVal::Entry(name) => g_pow(entry[name] as usize).into(),
            KVal::EndSentinel => g_pow(sentinel as usize).into(),
            KVal::Local(i) => g_pow((pc0 + i) as usize).into(),
            KVal::At(name, i) => g_pow((entry[name] + i) as usize).into(),
        }
    };
    match op {
        LOp::Set { o, k: kv } => Op::Set {
            o: *o,
            k: resolve_kval(kv),
        },
        LOp::Xor { a, b, c } => Op::Xor { a: *a, b: *b, c: *c },
        LOp::Mul { a, b, c } | LOp::Copy { src: a, one: b, dst: c } => Op::Mul { a: *a, b: *b, c: *c },
        // The known operand first: a range check's `MUL K = x·y` is the shape its proof reads.
        LOp::Solve { x, b, c } => Op::Mul { a: *b, b: *x, c: *c },
        LOp::Deref { o1, o2, o3, mode } => Op::Deref {
            o1: *o1,
            o2: *o2,
            o3: *o3,
            mode: *mode,
        },
        LOp::Slot { x, first, dst } => Op::Deref {
            o1: *x,
            o2: tables + first,
            o3: *dst,
            mode: DerefMode::Cell,
        },
        LOp::Jump { oc, od, of } => Op::Jump {
            oc: *oc,
            od: *od,
            of: *of,
        },
        LOp::DeferEnter { .. } | LOp::DeferWrite { .. } => unreachable!("expanded by `defer_tables`"),
        LOp::Keccak {
            m,
            tail,
            b8,
            cap,
            c,
            in_odd,
            out_odd,
            out_cells,
        } => Op::Keccak {
            m: *m,
            tail: *tail,
            b8: *b8,
            cap: *cap,
            out: *c,
            in_odd: *in_odd,
            out_odd: *out_odd,
            out_cells: *out_cells,
        },
    }
}
