//! The native verifiers on cases of run/: `harness CASE...`, for x86-64 or AArch64, linked with any of `xmss_verify`,
//! `sphincs_verify` and `leanvm_verify` (`run/check.sh` builds it: `rustc --cfg xmss --cfg sphincs --cfg vm` with the
//! assembled objects as link arguments, for `x86_64-unknown-linux-musl` or `aarch64-unknown-linux-musl`).
//!
//! Each case (the format of `reference/src/main.rs`) names its scheme and the expected bit. A signature case carries the
//! input words: the harness lays out the context as Native/Context.lean says (3200 words, 8-byte aligned, the input
//! words from byte 1024, every other word zero). A leanVM case names its bytecode, public input and wire files: the
//! harness lays out the context and the areas it points to as NativeVm/Input.lean says (`vm_layout`). Every area lies
//! between guard words. The harness calls the verifier through a wrapper that checks the callee-saved registers
//! survive (x86-64: rbx, rbp, r12..r15; AArch64: x19..x29, x30 holding the return address, and sp), checks the guard
//! words (and for leanVM the words the verifier only reads), and prints a line per case: `ok` or `MISMATCH`, the name,
//! the expected bit and the verifier's result (rax or x0).
//!
//! Exit codes: 0 every case agreed, 1 a mismatch, 2 a malformed case or a verifier not linked in, 3 a verifier broke its
//! contract (a result other than 0 or 1, a callee-saved register changed, a write outside its areas or to an input).

use std::ops::Range;
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

#[cfg(vm)]
unsafe extern "C" {
    fn leanvm_verify(ctx: *mut u64) -> u64;
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
const SAVED: &[&str] = &[
    "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29",
];
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

const GUARD_WORDS: usize = 512;
const GUARD: u64 = 0x5a5a_5a5a_5a5a_5a5a;

/// The signature verifiers' context: `Native/Context.lean`'s `ctxWords`, the input words from byte 1024.
const SIG_CTX_WORDS: usize = 3200;
const SIG_INPUT_WORD: usize = 1024 / 8;

#[cfg(xmss)]
const XMSS: Option<Verify> = Some(xmss_verify);
#[cfg(not(xmss))]
const XMSS: Option<Verify> = None;
#[cfg(sphincs)]
const SPHINCS: Option<Verify> = Some(sphincs_verify);
#[cfg(not(sphincs))]
const SPHINCS: Option<Verify> = None;
#[cfg(vm)]
const VM: Option<Verify> = Some(leanvm_verify);
#[cfg(not(vm))]
const VM: Option<Verify> = None;

/// The signature scheme's input words, and its verifier if linked in.
fn scheme(name: &str) -> Option<(usize, Option<Verify>)> {
    match name {
        "xmss" => Some((309, XMSS)),
        "sphincs" => Some((977, SPHINCS)),
        _ => None,
    }
}

/// Words between `GUARD_WORDS` guard words on each side, in one allocation; the verifier gets the inside.
struct Guarded(Vec<u64>);

impl Guarded {
    fn new(words: &[u64]) -> Self {
        let mut all = vec![GUARD; words.len() + 2 * GUARD_WORDS];
        all[GUARD_WORDS..GUARD_WORDS + words.len()].copy_from_slice(words);
        Guarded(all)
    }

    fn len(&self) -> usize {
        self.0.len() - 2 * GUARD_WORDS
    }

    fn words(&self) -> &[u64] {
        &self.0[GUARD_WORDS..GUARD_WORDS + self.len()]
    }

    /// The inside's address, in the allocation even when the inside is empty.
    fn addr(&mut self) -> *mut u64 {
        let n = self.len();
        self.0[GUARD_WORDS..GUARD_WORDS + n].as_mut_ptr()
    }

    fn guards_intact(&self) -> bool {
        let n = self.len();
        self.0[..GUARD_WORDS]
            .iter()
            .chain(&self.0[GUARD_WORDS + n..])
            .all(|&w| w == GUARD)
    }
}

/// The value of `key`, the next two tokens being `key` and the value.
fn field<'a>(tokens: &mut impl Iterator<Item = &'a str>, key: &str) -> Result<&'a str, String> {
    match (tokens.next(), tokens.next()) {
        (Some(k), Some(v)) if k == key => Ok(v),
        _ => Err(format!("bad case, no `{key}`")),
    }
}

/// Calls `verify` on the context at `ctx`; returns its result, noting in `faults` how it broke the calling convention.
fn call(verify: Verify, ctx: *mut u64, faults: &mut Vec<String>) -> u64 {
    let mut regs = vec![0u64; SAVED.len() + LINKAGE];
    // SAFETY: `verify` is a verifier given a context laid out for it, the areas it points to alive and apart; `regs`
    // has room for what `harness_call` writes.
    let result = unsafe { harness_call(verify, ctx, regs.as_mut_ptr()) };
    for (i, reg) in SAVED.iter().enumerate() {
        if regs[i] != PATTERN + i as u64 {
            faults.push(format!("callee-saved {reg} not preserved"));
        }
    }
    if let &[ret, sp, x30, sp_after] = &regs[SAVED.len()..] {
        if x30 != ret {
            faults.push("x30 not preserved".into());
        }
        if sp_after != sp {
            faults.push("sp not preserved".into());
        }
    }
    if result > 1 {
        faults.push(format!("{RESULT} {result}, not 0 or 1"));
    }
    result
}

/// Prints the case's line; returns 0 it agreed, else the exit code.
fn report(path: &str, expect: u64, result: u64, faults: &[String]) -> i32 {
    for fault in faults {
        eprintln!("harness: {path}: {fault}");
    }
    let status = if !faults.is_empty() {
        3
    } else {
        i32::from(result != expect)
    };
    let verdict = if status != 0 { "MISMATCH" } else { "ok" };
    println!("{verdict} {path} expect {expect} {RESULT} {result}");
    status
}

/// A signature case after its header: the verifier and the input words.
fn sig_case<'a>(name: &str, tokens: &mut impl Iterator<Item = &'a str>) -> Result<(Verify, Vec<u64>), String> {
    let n: usize = field(tokens, "words")?
        .parse()
        .map_err(|_| "bad word count".to_string())?;
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
    Ok((verify, input))
}

fn run_sig(path: &str, verify: Verify, expect: u64, input: &[u64]) -> i32 {
    let mut words = vec![0; SIG_CTX_WORDS];
    words[SIG_INPUT_WORD..SIG_INPUT_WORD + input.len()].copy_from_slice(input);
    let mut ctx = Guarded::new(&words);
    let mut faults = Vec::new();
    let result = call(verify, ctx.addr(), &mut faults);
    if !ctx.guards_intact() {
        faults.push("a write outside the context".into());
    }
    report(path, expect, result, &faults)
}

/// The leanVM verifier's context words: the transcript's `ctxEnd` (`NativeVm/Transcript/Layout.lean`, `ctxEnd_val`),
/// past the decoder's `cScr + Keccak.scratchWords = 116` (`NativeVm/Wire/Mem.lean`, `ctxN`).
const VM_CTX_WORDS: usize = 175;

/// The context words every part of the verifier keeps: those below the scratch (word 32) but the save area (`16 .. 21`)
/// (`Wire.Kept`, `NativeVm/Code/Contracts.lean`'s `Kept.ctx`).
const VM_KEPT: [Range<usize>; 2] = [0..16, 22..32];

/// What the leanVM verifier's other words hold before the call (the context's but its inputs and pointers, the decoded
/// and the working areas): words `BodyPre` only asks to be there, so not zero, which nothing may rely on.
const JUNK: u64 = 0xa5a5_a5a5_a5a5_a5a5;

/// `decodedWords L` (`NativeVm/Input.lean`): the stream's count and `maxStream L = L / 16` elements of two words, the
/// phase count, then `wireMaxPhases = 8` phases of `phaseWords = 3 + wireMaxQueries · openingWords` words,
/// `openingWords = 1 + wireMaxLeafWords + 4 · wireMaxHeight`, with `wireMaxQueries = 256`, `wireMaxLeafWords = 64`,
/// `wireMaxHeight = 32` (`LeanVM/Wire/Encoding.lean`).
fn vm_decoded_words(l: usize) -> usize {
    let opening = 1 + 64 + 4 * 32;
    1 + 2 * (l / 16) + 1 + 8 * (3 + 256 * opening)
}

/// `NativeVm.Code.workWords n` (`NativeVm/Code/Data.lean`): `max (max Wire.workWords (n + 2)) dataEnd`, with
/// `Wire.workWords = 60720` (`NativeVm/Wire/Code.lean`) and `dataEnd = 85438` (`dataEnd_val`).
fn vm_work_words(n: usize) -> usize {
    (n + 2).max(60720).max(85438)
}

/// Bytes packed little-endian into words, the last word's bytes past the end zero.
fn le_words(bytes: &[u8]) -> Vec<u64> {
    bytes
        .chunks(8)
        .map(|chunk| chunk.iter().rev().fold(0, |w, &b| (w << 8) | u64::from(b)))
        .collect()
}

/// A leanVM case after its header: the bytecode's words, the public input's four words, the wire's bytes.
fn vm_case<'a>(tokens: &mut impl Iterator<Item = &'a str>) -> Result<(Vec<u64>, Vec<u64>, Vec<u8>), String> {
    let mut read = |key: &str| {
        let file = field(tokens, key)?;
        fs::read(file).map_err(|e| format!("{file}: {e}"))
    };
    let (bytecode, public, wire) = (read("bytecode")?, read("public")?, read("wire")?);
    if bytecode.len() % 8 != 0 {
        return Err("the bytecode is not whole words".into());
    }
    if public.len() != 32 {
        return Err("the public input is not 32 bytes".into());
    }
    Ok((le_words(&bytecode), le_words(&public), wire))
}

/// Lays out a leanVM case as `NativeVm/Input.lean` says, each area between guard words: the context of
/// `VM_CTX_WORDS` words holds the wire's address and byte count `L` (words `0`, `1`), the bytecode's address and word
/// count (`2`, `3`), the public input (`4 .. 7`), the decoded area's address and its `vm_decoded_words L` words (`8`,
/// `9`), the working area's address and its `vm_work_words` of the bytecode's count (`10`, `11`), every other word
/// `JUNK`; the wire's bytes packed as `le_words`. Checks the guard words, the wire and the bytecode, and the context's
/// `VM_KEPT` words after the call.
fn run_vm(path: &str, verify: Verify, expect: u64, bytecode: &[u64], public: &[u64], wire: &[u8]) -> i32 {
    let wire_words = le_words(wire);
    let mut wire_area = Guarded::new(&wire_words);
    let mut bytecode_area = Guarded::new(bytecode);
    let mut decoded = Guarded::new(&vec![JUNK; vm_decoded_words(wire.len())]);
    let mut work = Guarded::new(&vec![JUNK; vm_work_words(bytecode.len())]);
    let mut words = vec![JUNK; VM_CTX_WORDS];
    words[0] = wire_area.addr() as u64;
    words[1] = wire.len() as u64;
    words[2] = bytecode_area.addr() as u64;
    words[3] = bytecode.len() as u64;
    words[4..8].copy_from_slice(public);
    words[8] = decoded.addr() as u64;
    words[9] = decoded.len() as u64;
    words[10] = work.addr() as u64;
    words[11] = work.len() as u64;
    let mut ctx = Guarded::new(&words);

    let mut faults = Vec::new();
    let result = call(verify, ctx.addr(), &mut faults);
    let areas = [
        ("context", &ctx),
        ("wire", &wire_area),
        ("bytecode", &bytecode_area),
        ("decoded area", &decoded),
        ("working area", &work),
    ];
    for (name, area) in areas {
        if !area.guards_intact() {
            faults.push(format!("a write next to the {name}"));
        }
    }
    if wire_area.words() != wire_words {
        faults.push("a write to the wire".into());
    }
    if bytecode_area.words() != bytecode {
        faults.push("a write to the bytecode".into());
    }
    for kept in VM_KEPT {
        if ctx.words()[kept.clone()] != words[kept.clone()] {
            faults.push(format!("a write to the context's words {kept:?}"));
        }
    }
    report(path, expect, result, &faults)
}

/// A parsed case: a signature verifier and its input words, or the leanVM verifier and its bytecode's words, public
/// input words and wire bytes.
enum Case {
    Sig(Verify, Vec<u64>),
    Vm(Verify, Vec<u64>, Vec<u64>, Vec<u8>),
}

/// A case's expected bit and inputs.
fn parse(text: &str) -> Result<(u64, Case), String> {
    let mut tokens = text.split_ascii_whitespace();
    let name = field(&mut tokens, "scheme")?;
    let expect = match field(&mut tokens, "expect")? {
        "0" => 0,
        "1" => 1,
        e => return Err(format!("expect {e}, not 0 or 1")),
    };
    let case = if name == "vm" {
        let verify = VM.ok_or("leanvm_verify is not linked in")?;
        let (bytecode, public, wire) = vm_case(&mut tokens)?;
        Case::Vm(verify, bytecode, public, wire)
    } else {
        let (verify, input) = sig_case(name, &mut tokens)?;
        Case::Sig(verify, input)
    };
    if tokens.next().is_some() {
        return Err("text after the case".to_string());
    }
    Ok((expect, case))
}

/// Runs one case: 0 it agreed, else the exit code.
fn run(path: &str) -> i32 {
    match fs::read_to_string(path)
        .map_err(|e| e.to_string())
        .and_then(|text| parse(&text))
    {
        Ok((expect, Case::Sig(verify, input))) => run_sig(path, verify, expect, &input),
        Ok((expect, Case::Vm(verify, bytecode, public, wire))) => {
            run_vm(path, verify, expect, &bytecode, &public, &wire)
        }
        Err(e) => {
            eprintln!("harness: {path}: {e}");
            2
        }
    }
}

fn main() {
    let cases: Vec<String> = env::args().skip(1).collect();
    if cases.is_empty() {
        eprintln!("usage: harness CASE...");
        process::exit(2);
    }
    process::exit(cases.iter().map(|case| run(case)).max().unwrap_or(0));
}
