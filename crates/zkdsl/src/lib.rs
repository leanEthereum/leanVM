//! The zkDSL (see `zkDSL.md`): its parser ([`parse`], [`parse_with_replacements`], [`parse_const`], [`f128_literal`]),
//! the [`Ast`] it gives, and a bytecode disassembler ([`disassemble`]).
//!
//! The compiler is the Lean back end (`formal/lean_vm/LeanVM/Compiler`), which compiles this parser's AST (exported by
//! `formal/lean_vm/scripts/guest-export`) through Lean's front end (`LeanVM/Core/Expand.lean`).

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;

use field::{Base, Consts, F64, F128, as_base};
use isa::pretty_integer;
use isa::{DerefMode, Op};

mod ast;
mod field;
mod parser;
pub use ast::*;
pub use parser::{f128_literal, parse, parse_const, parse_with_constants, parse_with_replacements};

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
