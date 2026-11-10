//! A compiler from a Python-like zkDSL (see `zkDSL.md`) to the ISA (`cpu::Op`).
//! Produces a [`leanvm_core::cpu::Program`]: bytecode plus the prover's allocation hints.
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

use leanvm_core::cpu::hints::{BitsDest, RHint};
use leanvm_core::cpu::{DerefMode, Op, OutCells, Program};
use primitives::{
    field::{F64, F128, g_pow},
    pretty_integer,
};

mod ast;
mod ir;
mod lower;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{f128_literal, parse, parse_const, parse_with_replacements};

/// Compile an [`Ast`] to a provable [`Program`]. Panics on a malformed program
/// (unbound variable, missing `main`, address overflow).
pub fn compile(ast: &Ast) -> Program {
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
    let dbg_lower = std::env::var("DBG_LOWER").is_ok();

    let mut loop_bounds = HashMap::new();
    let mut loop_ctr = 0usize;
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
            &mut loop_ctr,
            &defs,
            &const_arrays,
            &mut loop_bounds,
            &mut tables,
        ));
    }
    // The tables sit past `main`'s own cells. At pc 0, in `main`'s frame (`fp = g^0`),
    // one `SET` per slot writes them, then falls through into `main`.
    let tables_base = lowered[0].frame_size;
    if !tables.slots.is_empty() {
        lowered[0].frame_size += tables.slots.len() as u32;
        let code = (tables.slots.iter().zip(tables_base..))
            .map(|(k, o)| LInstr {
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
            },
        );
    }
    if dbg_lower {
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
                                    size: size
                                        .checked_mul(u32::try_from(n - 1).expect("loop range too large"))
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
                        Hint::AllocFrameMax { ptr, callees } => RHint::Alloc {
                            ptr,
                            size: callees.iter().map(|c| frame_size[c]).max().unwrap(),
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
    let mut program = Program::assemble(prog, hints, frame_size["main"]);
    program.src_lines = src_lines;
    program.fn_ranges = lowered
        .iter()
        .map(|l| (l.name.clone(), entry[&l.name], l.code.len() as u32))
        .collect();
    program
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
        acc *= F64::G;
    }
    // A machine word is 128-bit; K-valued immediates (high limb zero) may be small
    // g-powers (code addresses, indices), shown as `gʲ`.
    let kfmt = |k: F128| match k.as_base() {
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
            // embed them canonically as (c0, 0, 0).
            KVal::Entry(name) => g_pow(entry[name] as usize).into(),
            KVal::EndSentinel => g_pow(sentinel as usize).into(),
            KVal::Local(i) => g_pow((pc0 + i) as usize).into(),
            KVal::At(name, i) => g_pow((entry[name] + i) as usize).into(),
        }
    };
    match op {
        LOp::MulNextFrame { a, b, c } => Op::Mul {
            a: *a,
            b: *b,
            c: frame_size.checked_add(*c).expect("frame offset overflow"),
        },
        LOp::Set { o, k: kv } => Op::Set {
            o: *o,
            k: resolve_kval(kv),
        },
        LOp::Xor { a, b, c } => Op::Xor { a: *a, b: *b, c: *c },
        LOp::Mul { a, b, c } => Op::Mul { a: *a, b: *b, c: *c },
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
