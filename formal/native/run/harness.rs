//! The native verifiers on cases of run/: `harness CASE...`, for x86-64 or AArch64, linked with `xmss_verify`,
//! `sphincs_verify` or both (`run/check.sh` builds it: `rustc --cfg xmss --cfg sphincs` with the assembled objects as
//! link arguments, for `x86_64-unknown-linux-musl` or `aarch64-unknown-linux-musl`).
//!
//! Each case (the format of `reference/src/main.rs`) names its scheme, the expected bit and the input words. The harness
//! lays out the context as Native/Context.lean says (3200 words, 8-byte aligned, the input words from byte 1024, every
//! other word zero), between guard words, calls the scheme's verifier through a wrapper that checks the callee-saved
//! registers survive (x86-64: rbx, rbp, r12..r15; AArch64: x19..x29, x30 holding the return address, and sp), and
//! prints a line per case: `ok` or `MISMATCH`, the name, the expected bit and the verifier's result (rax or x0).
//!
//! Exit codes: 0 every case agreed, 1 a mismatch, 2 a malformed case or a verifier not linked in, 3 a verifier broke its
//! contract (a result other than 0 or 1, a callee-saved register changed, a write outside the context).

use std::{env, fs, process};

type Verify = unsafe extern "C" fn(*mut u64) -> u64;

#[cfg(xmss)]
unsafe extern "C" {
    fn xmss_verify(ctx: *mut u64) -> u64;
}

#[cfg(sphincs)]
unsafe extern "C" {
    fn sphincs_verify(ctx: *mut u64) -> u64;
}

unsafe extern "C" {
    /// `harness_call(verify, ctx, regs)`: `verify(ctx)` with the callee-saved registers set to `PATTERN + i`, the
    /// i-th of `SAVED`, which it writes to `regs[i]` after the call; on AArch64 also `regs[SAVED..SAVED + 4]`: the
    /// return address `verify` was given and sp before the call, then x30 and sp after it.
    fn harness_call(verify: Verify, ctx: *mut u64, regs: *mut u64) -> u64;
}

const PATTERN: u64 = 0x0123_4567_89ab_cde1;

#[cfg(target_arch = "x86_64")]
const SAVED: &[&str] = &["rbx", "rbp", "r12", "r13", "r14", "r15"];
#[cfg(target_arch = "x86_64")]
const RESULT: &str = "rax";
#[cfg(target_arch = "x86_64")]
const LINKAGE: usize = 0;

// Seven pushes keep the stack 16-byte aligned at the call.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".text",
    ".globl harness_call",
    ".type harness_call, @function",
    "harness_call:",
    "  push %rbx",
    "  push %rbp",
    "  push %r12",
    "  push %r13",
    "  push %r14",
    "  push %r15",
    "  push %rdx",
    "  mov %rdi, %rax",
    "  mov %rsi, %rdi",
    "  movabs $0x0123456789abcde1, %rbx",
    "  movabs $0x0123456789abcde2, %rbp",
    "  movabs $0x0123456789abcde3, %r12",
    "  movabs $0x0123456789abcde4, %r13",
    "  movabs $0x0123456789abcde5, %r14",
    "  movabs $0x0123456789abcde6, %r15",
    "  call *%rax",
    "  pop %rdx",
    "  mov %rbx, 0(%rdx)",
    "  mov %rbp, 8(%rdx)",
    "  mov %r12, 16(%rdx)",
    "  mov %r13, 24(%rdx)",
    "  mov %r14, 32(%rdx)",
    "  mov %r15, 40(%rdx)",
    "  pop %r15",
    "  pop %r14",
    "  pop %r13",
    "  pop %r12",
    "  pop %rbp",
    "  pop %rbx",
    "  ret",
    ".size harness_call, .-harness_call",
    options(att_syntax)
);

#[cfg(target_arch = "aarch64")]
const SAVED: &[&str] = &["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29"];
#[cfg(target_arch = "aarch64")]
const RESULT: &str = "x0";
#[cfg(target_arch = "aarch64")]
const LINKAGE: usize = 4;

// The frame keeps the harness's own x19..x30; `regs` and the frame's sp wait in `harness_saved` rather than in a
// register or on the stack, which the verifier may break, so the wrapper returns whatever it left there.
#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".bss",
    ".p2align 3",
    "harness_saved:",
    "  .zero 16",
    ".text",
    ".globl harness_call",
    ".type harness_call, %function",
    ".p2align 2",
    "harness_call:",
    "  stp x29, x30, [sp, #-96]!",
    "  stp x19, x20, [sp, #16]",
    "  stp x21, x22, [sp, #32]",
    "  stp x23, x24, [sp, #48]",
    "  stp x25, x26, [sp, #64]",
    "  stp x27, x28, [sp, #80]",
    "  adrp x9, harness_saved",
    "  add x9, x9, :lo12:harness_saved",
    "  mov x10, sp",
    "  stp x2, x10, [x9]",
    "  adr x11, 1f",
    "  stp x11, x10, [x2, #88]",
    "  mov x16, x0",
    "  mov x0, x1",
    "  movz x19, #0xcde1",
    "  movk x19, #0x89ab, lsl #16",
    "  movk x19, #0x4567, lsl #32",
    "  movk x19, #0x0123, lsl #48",
    "  add x20, x19, #1",
    "  add x21, x19, #2",
    "  add x22, x19, #3",
    "  add x23, x19, #4",
    "  add x24, x19, #5",
    "  add x25, x19, #6",
    "  add x26, x19, #7",
    "  add x27, x19, #8",
    "  add x28, x19, #9",
    "  add x29, x19, #10",
    "  blr x16",
    "1:",
    "  adrp x9, harness_saved",
    "  add x9, x9, :lo12:harness_saved",
    "  ldp x2, x10, [x9]",
    "  stp x19, x20, [x2]",
    "  stp x21, x22, [x2, #16]",
    "  stp x23, x24, [x2, #32]",
    "  stp x25, x26, [x2, #48]",
    "  stp x27, x28, [x2, #64]",
    "  str x29, [x2, #80]",
    "  mov x11, sp",
    "  stp x30, x11, [x2, #104]",
    "  mov sp, x10",
    "  ldp x19, x20, [sp, #16]",
    "  ldp x21, x22, [sp, #32]",
    "  ldp x23, x24, [sp, #48]",
    "  ldp x25, x26, [sp, #64]",
    "  ldp x27, x28, [sp, #80]",
    "  ldp x29, x30, [sp], #96",
    "  ret",
    ".size harness_call, .-harness_call",
);

const CTX_WORDS: usize = 3200;
const INPUT_WORD: usize = 1024 / 8;
const GUARD_WORDS: usize = 512;
const GUARD: u64 = 0x5a5a_5a5a_5a5a_5a5a;

#[cfg(xmss)]
const XMSS: Option<Verify> = Some(xmss_verify);
#[cfg(not(xmss))]
const XMSS: Option<Verify> = None;
#[cfg(sphincs)]
const SPHINCS: Option<Verify> = Some(sphincs_verify);
#[cfg(not(sphincs))]
const SPHINCS: Option<Verify> = None;

/// The scheme's input words, and its verifier if linked in.
fn scheme(name: &str) -> Option<(usize, Option<Verify>)> {
    match name {
        "xmss" => Some((309, XMSS)),
        "sphincs" => Some((977, SPHINCS)),
        _ => None,
    }
}

/// A case's verifier, expected bit and input words.
fn parse(text: &str) -> Result<(Verify, u64, Vec<u64>), String> {
    let mut tokens = text.split_ascii_whitespace();
    let mut field = |key: &str| match (tokens.next(), tokens.next()) {
        (Some(k), Some(v)) if k == key => Ok(v),
        _ => Err(format!("bad header, no `{key}`")),
    };
    let name = field("scheme")?;
    let expect = match field("expect")? {
        "0" => 0,
        "1" => 1,
        e => return Err(format!("expect {e}, not 0 or 1")),
    };
    let n: usize = field("words")?.parse().map_err(|_| "bad word count".to_string())?;
    let (words, verify) = scheme(name).ok_or_else(|| format!("unknown scheme {name}"))?;
    if n != words {
        return Err(format!("scheme {name} with {n} words"));
    }
    let verify = verify.ok_or_else(|| format!("{name}_verify is not linked in"))?;
    let input = (0..n)
        .map(|i| {
            let w = tokens.next().ok_or_else(|| format!("word {i} missing"))?;
            u64::from_str_radix(w, 16).map_err(|_| format!("word {i} is not hex"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if tokens.next().is_some() {
        return Err("text after the words".to_string());
    }
    Ok((verify, expect, input))
}

/// Runs one case: 0 it agreed, else the exit code.
fn run(path: &str) -> i32 {
    let parsed = fs::read_to_string(path).map_err(|e| e.to_string()).and_then(|text| parse(&text));
    let (verify, expect, input) = match parsed {
        Ok(case) => case,
        Err(e) => {
            eprintln!("harness: {path}: {e}");
            return 2;
        }
    };

    let mut area = vec![GUARD; GUARD_WORDS + CTX_WORDS + GUARD_WORDS];
    let ctx = &mut area[GUARD_WORDS..GUARD_WORDS + CTX_WORDS];
    ctx.fill(0);
    ctx[INPUT_WORD..INPUT_WORD + input.len()].copy_from_slice(&input);

    let mut regs = vec![0u64; SAVED.len() + LINKAGE];
    // SAFETY: `verify` is a verifier of this scheme, given a context of `CTX_WORDS` words; `regs` has room for what
    // `harness_call` writes.
    let result = unsafe { harness_call(verify, ctx.as_mut_ptr(), regs.as_mut_ptr()) };

    let mut status = 0;
    for (i, reg) in SAVED.iter().enumerate() {
        if regs[i] != PATTERN + i as u64 {
            eprintln!("harness: {path}: callee-saved {reg} not preserved");
            status = 3;
        }
    }
    if let &[ret, sp, x30, sp_after] = &regs[SAVED.len()..] {
        if x30 != ret {
            eprintln!("harness: {path}: x30 not preserved");
            status = 3;
        }
        if sp_after != sp {
            eprintln!("harness: {path}: sp not preserved");
            status = 3;
        }
    }
    let (below, rest) = area.split_at(GUARD_WORDS);
    if below.iter().chain(&rest[CTX_WORDS..]).any(|&w| w != GUARD) {
        eprintln!("harness: {path}: a write outside the context");
        status = 3;
    }
    if result > 1 {
        eprintln!("harness: {path}: {RESULT} {result}, not 0 or 1");
        status = 3;
    }
    if status == 0 && result != expect {
        status = 1;
    }
    let verdict = if status != 0 { "MISMATCH" } else { "ok" };
    println!("{verdict} {path} expect {expect} {RESULT} {result}");
    status
}

fn main() {
    let cases: Vec<String> = env::args().skip(1).collect();
    if cases.is_empty() {
        eprintln!("usage: harness CASE...");
        process::exit(2);
    }
    process::exit(cases.iter().map(|case| run(case)).max().unwrap_or(0));
}
