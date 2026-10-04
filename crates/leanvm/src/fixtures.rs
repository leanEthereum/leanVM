//! The programs the tests prove, and the runs they share.

use crate::asm::{Add, Addi, Asm, Bne, Ld, Reg, Sd};
use crate::{Output, Program, ProvenRun, Prover, Rate, Region};
use leanvm_guest::PublicValues;
use std::sync::OnceLock;

/// A program leaving F(n) mod 2^64 in a0, with n the first word of its RAM image.
///
/// Its loop keeps the two last numbers on the stack, so its rows reach loads and stores.
pub(crate) fn fibonacci(n: u64) -> Program {
    // RAM of 2^4 words: n at its base, the two numbers at its top.
    const LOG_RAM: usize = 4;
    let text = Asm::new()
        // sp points at the top two words, t0 reads n from the image.
        .li(Reg::SP, Region::RAM.base() + (8 << LOG_RAM) - 16)
        .li(Reg::T0, Region::RAM.base())
        .load(Ld, Reg::T0, 0, Reg::T0)
        // The stack starts at (F(0), F(1)) = (0, 1).
        .i(Addi, Reg::T1, Reg::ZERO, 1)
        .store(Sd, Reg::ZERO, 0, Reg::SP)
        .store(Sd, Reg::T1, 8, Reg::SP)
        // One step: (a, b) -> (b, a + b), n times.
        .label("loop")
        .load(Ld, Reg::A0, 0, Reg::SP)
        .load(Ld, Reg::A1, 8, Reg::SP)
        .r(Add, Reg::A2, Reg::A0, Reg::A1)
        .store(Sd, Reg::A1, 0, Reg::SP)
        .store(Sd, Reg::A2, 8, Reg::SP)
        .i(Addi, Reg::T0, Reg::T0, -1)
        .branch(Bne, Reg::T0, Reg::ZERO, "loop")
        // The output is (F(n), 0, 0, 0).
        .load(Ld, Reg::A0, 0, Reg::SP)
        .li(Reg::A1, 0)
        .li(Reg::A2, 0)
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![n], LOG_RAM, 0).expect("a program")
}

/// The proven run of F(90), made once and shared by every test.
pub(crate) fn fibonacci_run() -> &'static ProvenRun {
    static RUN: OnceLock<ProvenRun> = OnceLock::new();
    RUN.get_or_init(|| {
        Prover::new(Rate::MIN)
            .prove(&fibonacci(90), &[])
            .expect("the run exits")
    })
}

/// The preimage guest, its advice holding a message, and the output it must give.
///
/// The guest hashes the message and commits the digest.
///
/// Its rows reach what the Fibonacci program leaves out: the hash table and the advice.
pub(crate) fn preimage(message: &[u8]) -> (Program, Vec<u64>, Output) {
    let program = Program::from_elf(include_bytes!("../../../programs/preimage/preimage.elf")).expect("a guest");

    // The advice: the length, then the message in little-endian words, zero-padded.
    //
    //     "leanVM"  →  [6, 0x0000_4d56_6e61_656c]
    let words = message.chunks(8).map(|chunk| {
        let mut word = [0; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        u64::from_le_bytes(word)
    });
    let advice = std::iter::once(message.len() as u64).chain(words).collect();

    // The output: the digest of what the guest commits, which is the message's digest.
    let digest = primitives::hash::hash(message);
    let digest: [u64; 4] =
        std::array::from_fn(|i| u64::from_le_bytes(*digest[8 * i..].first_chunk().expect("32 bytes")));
    let mut public = PublicValues::new();
    public.commit(&digest);
    (program, advice, Output::new(public.digest()))
}
