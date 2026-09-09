//! A compiler from a Python-like zkDSL (see `zkDSL.md`) to the ISA (`cpu::Op`).
//! Produces a [`lean_vm::cpu::Program`]: bytecode plus the prover's allocation hints.
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

use lean_vm::cpu::hints::{BitsDest, RHint};
use lean_vm::cpu::{DerefMode, Op, Program};
use primitives::{
    field::{F64, F192, g_pow},
    pretty_integer,
};

mod ast;
pub mod filler;
mod ir;
mod lower;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{parse, parse_const, parse_file_with_replacements, parse_with_replacements};

/// Compile an [`Ast`] to a provable [`Program`]. Panics on a malformed program
/// (unbound variable, missing `main`, address overflow).
pub fn compile(ast: &Ast) -> Program {
    // Every program carries, past `main`'s halt, the fill blocks that bring each table's
    // row count up to a power of two, so that no table needs padding rows (see `filler`).
    compile_inner(ast, true)
}

/// [`compile`] without the fill blocks, so the program's own instruction mix is what
/// runs. Used by tests of instruction selection and execution.
pub fn compile_without_filler(ast: &Ast) -> Program {
    compile_inner(ast, false)
}

fn compile_inner(ast: &Ast, with_filler: bool) -> Program {
    // Lower main first (entry pc 0), then the rest, expanding loop helpers.
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
    let defs: HashMap<String, &Func> = ast.funcs.iter().map(|f| (f.name.clone(), f)).collect();
    // Constant arrays by name, resolved at lowering (`NAME[i]`, `len(NAME)`).
    let const_arrays: HashMap<String, &[F192]> = ast
        .const_arrays
        .iter()
        .map(|(name, values)| (name.clone(), values.as_slice()))
        .collect();
    let dbg_lower = std::env::var("DBG_LOWER").is_ok();

    let mut loop_ctr = 0usize;
    let mut lowered: Vec<Lowered> = Vec::new();
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
        let low = lower_func(&f, &mut queue, &mut loop_ctr, &defs, &const_arrays, with_filler);
        if dbg_lower {
            eprintln!("== fn {} (frame {}) ==", low.name, pretty_integer(low.frame_size));
            for (i, ins) in low.code.iter().enumerate() {
                let index = pretty_integer(i);
                eprintln!("  {index:>5}: {:?}", ins.op);
            }
        }
        lowered.push(low);
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
    // `EndSentinel` jump dest resolves to it, and the program halts there.
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
        let base = entry[&l.name];
        for ins in &mut l.code {
            let here = prog.len() as u32;
            if !ins.hints.is_empty() {
                let rhs = ins
                    .hints
                    .drain(..)
                    .map(|h| match h {
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
            prog.push(resolve(&ins.op, &entry, sentinel, base));
        }
    }

    // Pad the bytecode to `B` (the sentinel slot g^{B-1} must exist for execution).
    prog.resize(bytecode_size, Op::Set { o: 0, k: F192::ZERO });
    let mut program = Program::assemble(prog, hints, frame_size["main"]);
    program.src_lines = src_lines;
    program.fn_ranges = lowered
        .iter()
        .map(|l| (l.name.clone(), entry[&l.name], l.code.len() as u32))
        .collect();
    // The blocks are `main`'s, and `main` is lowered first, so its entry pc is 0 and the
    // block pcs are already the global ones.
    program.filler = std::mem::take(&mut lowered[0].filler);
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
        acc *= primitives::field::G;
    }
    // A machine word is 192-bit; K-valued immediates (both high limbs zero) may be small
    // g-powers (code addresses, indices), shown as `gʲ`.
    let kfmt = |k: F192| match (k.c1 == 0 && k.c2 == 0).then(|| gmap.get(&F64(k.c0))).flatten() {
        Some(j) => format!("g^{j}"),
        None if k.c1 == 0 && k.c2 == 0 => format!("0x{:016x}", k.c0),
        None => format!("0x{:016x}{:016x}{:016x}", k.c2, k.c1, k.c0),
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
            Op::Blake2s { ins, cv, out, md } => {
                format!(
                    "BLAKE2S fp[{out}..]= compress(cv=fp[{cv}..], m=fp[{}],fp[{}],fp[{}],fp[{}], meta=fp[{md}])",
                    ins[0], ins[1], ins[2], ins[3]
                )
            }
        };
        writeln!(out, "{:>6}  {line}", pretty_integer(pc)).unwrap();
    }
    out
}

/// Embed a `u128` source literal into the low 128 bits of a 192-bit machine word.
pub(crate) fn lit_field(n: u128) -> F192 {
    F192::new(n as u64, (n >> 64) as u64, 0)
}

/// `g^e` for a `u128` exponent (square-and-multiply). `field::g_pow` only takes
/// a `usize`; an index carried in the exponent (a Fibonacci number, say) can
/// exceed 64 bits (`ord(g) = 2^64 − 1`, so the exponent wraps mod that).
fn g_pow_u128(mut e: u128) -> F64 {
    let mut result = F64::ONE;
    let mut base = primitives::field::G;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

fn resolve(op: &LOp, entry: &HashMap<String, u32>, sentinel: u32, base: u32) -> Op {
    let resolve_kval = |kv: &KVal| -> F192 {
        match kv {
            KVal::Const(c) => *c,
            // Address / entry / sentinel constants are K-valued g-powers;
            // embed them canonically as (c0, 0, 0).
            KVal::Entry(name) => g_pow(entry[name] as usize).into(),
            KVal::EndSentinel => g_pow(sentinel as usize).into(),
            KVal::Local(i) => g_pow((base + i) as usize).into(),
        }
    };
    match op {
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
        LOp::Jump { oc, od, of } => Op::Jump {
            oc: *oc,
            od: *od,
            of: *of,
        },
        LOp::Blake2s { ins, cv, c, md } => Op::Blake2s {
            ins: *ins,
            cv: *cv,
            out: *c,
            md: *md,
        },
    }
}
