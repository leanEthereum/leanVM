//! `isa-random`: programs from the generator: straight-line code over main's frame, forward jumps over dead garbage,
//! untaken jumps, calls into frames of their own, KECCAK rows over canonical cells, and now and then a deliberate
//! mistake.

use super::program::{Builder, Exit, garbage};
use crate::{Ctx, Outcome, Source};
use leanvm_core::cpu::Op;
use primitives::field::F192;

/// Where callee frames start: above every cell main uses.
const FRAMES: u32 = 1 << 13;
const FRAME: u32 = 1 << 11;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let public_input = public_input(src);
    let mut b = Builder::new(public_input);
    let steps = src.size(80);
    let mut calls = 0;
    for _ in 0..steps {
        match src.below(40) {
            0 | 1 => {
                let n = src.range(1, 6);
                b.skip(src, n);
                ctx.note("skip");
            }
            2 => {
                b.untaken(src);
                ctx.note("untaken");
            }
            3 | 4 if calls < 4 => {
                let exit = match src.below(20) {
                    0 => Exit::HaltMain,
                    1 => Exit::HaltHere,
                    _ => Exit::Return,
                };
                let body = src.size(12);
                b.call(src, FRAMES + calls * FRAME, body, exit);
                calls += 1;
                ctx.note(format!("call {exit:?}"));
            }
            5 if src.chance(1, 3) => {
                b.main.mistake(src);
                ctx.note("mistake");
            }
            _ => b.main.step(src),
        }
        if b.main.code.len() > 400 {
            break;
        }
    }
    let halt = if src.chance(3, 4) {
        Op::Xor { a: 0, b: 0, c: 0 }
    } else {
        garbage(src)
    };
    let min_len = 1 << src.below(8);
    let built = b.finish(src, min_len, halt);
    let main_frame = match src.below(5) {
        0 => src.below(3) as u32,
        1 => built.cells,
        2 => src.below(1 << 16) as u32,
        _ => 64,
    };
    ctx.note(format!("len {}", built.prog.len().trailing_zeros()));
    let program = built.program(main_frame);
    super::check(&program, public_input, Some(&built), src, ctx, "isa-random")
}

/// A statement: two 128-bit halves, often small or zero.
pub fn public_input(src: &mut Source) -> [F192; 2] {
    std::array::from_fn(|_| match src.below(4) {
        0 => F192::ZERO,
        1 => F192::new(src.edgy_u64(), 0, 0),
        _ => F192::new(src.u64(), src.u64(), 0),
    })
}
