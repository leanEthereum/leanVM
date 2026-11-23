//! The rustc verifiers on cases of run/: `harness CASE...`, for x86-64 or AArch64, linked with any of `xmss_verify`,
//! `sphincs_verify` and `leanvm_verify` (`run/check.sh` builds it: `rustc --cfg xmss --cfg sphincs --cfg vm` with the
//! assembled objects as link arguments, for `x86_64-unknown-linux-musl` or `aarch64-unknown-linux-musl`).
//!
//! Each case (the format of `reference/src/main.rs`) names its scheme and the expected bit. A signature case carries the
//! input words: the harness lays out the read-only context as `rustc/xmss.rs` and `rustc/sphincs.rs` require, with
//! input words from byte 1024. A leanVM case names its bytecode, public input and wire files: the harness lays out
//! the 12-word read-only context and its areas as `rustc/vm/src/lib.rs` requires. Every area lies between guard pages.
//! The harness calls the verifier through a wrapper that checks the callee-saved registers
//! survive (x86-64: rbx, rbp, r12..r15; AArch64: x19..x29, x30 holding the return address, and sp), checks the guard
//! words (and for leanVM the words the verifier only reads), and prints a line per case: `ok` or `MISMATCH`, the name,
//! the expected bit and the verifier's result (rax or x0).
//!
//! Exit codes: 0 every case agreed, 1 a mismatch, 2 a malformed case or a verifier not linked in, 3 a verifier broke its
//! contract (a result other than 0 or 1, a callee-saved register changed, a write outside its areas or to an input).

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
const LINKAGE: usize = 3;

// Six callee-saved pushes plus `sub $8, %rsp` keep %rsp 16-byte aligned at `call *%rax`.
// `regs` and the pre-call `%rsp` wait in `.bss` (`harness_saved`) so a broken `%rsp` is captured and reported
// cleanly instead of crashing. Caller-saved registers are poisoned before the call so `ctx`/`regs` do not leak.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".bss",
    ".p2align 3",
    "harness_saved:",
    "  .zero 16",
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
    "  sub $8, %rsp",
    "  lea harness_saved(%rip), %r10",
    "  mov %rdx, 0(%r10)",
    "  mov %rsp, 8(%r10)",
    "  mov %rsp, 48(%rdx)",
    "  mov %rdi, %rax",
    "  mov %rsi, %rdi",
    "  movabs $0x0123456789abcde1, %rbx",
    "  movabs $0x0123456789abcde2, %rbp",
    "  movabs $0x0123456789abcde3, %r12",
    "  movabs $0x0123456789abcde4, %r13",
    "  movabs $0x0123456789abcde5, %r14",
    "  movabs $0x0123456789abcde6, %r15",
    "  movabs $0xdeadbeefcafe0001, %rsi",
    "  movabs $0xdeadbeefcafe0002, %rdx",
    "  movabs $0xdeadbeefcafe0003, %rcx",
    "  movabs $0xdeadbeefcafe0004, %r8",
    "  movabs $0xdeadbeefcafe0005, %r9",
    "  movabs $0xdeadbeefcafe0006, %r10",
    "  movabs $0xdeadbeefcafe0007, %r11",
    "  call *%rax",
    "  mov %rsp, %r11",
    "  lea harness_saved(%rip), %r10",
    "  mov 0(%r10), %rdx",
    "  mov 8(%r10), %rsp",
    "  pushfq",
    "  pop %rcx",
    "  mov %rbx, 0(%rdx)",
    "  mov %rbp, 8(%rdx)",
    "  mov %r12, 16(%rdx)",
    "  mov %r13, 24(%rdx)",
    "  mov %r14, 32(%rdx)",
    "  mov %r15, 40(%rdx)",
    "  mov %r11, 56(%rdx)",
    "  mov %rcx, 64(%rdx)",
    "  add $8, %rsp",
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
// Caller-saved registers x1..x15 and x17 are poisoned before `blr x16` so `ctx`/`regs` do not leak.
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
    "  movz x1, #0x0001",
    "  movk x1, #0xcafe, lsl #16",
    "  movk x1, #0xbeef, lsl #32",
    "  movk x1, #0xdead, lsl #48",
    "  add x2, x1, #1",
    "  add x3, x1, #2",
    "  add x4, x1, #3",
    "  add x5, x1, #4",
    "  add x6, x1, #5",
    "  add x7, x1, #6",
    "  add x8, x1, #7",
    "  add x9, x1, #8",
    "  add x10, x1, #9",
    "  add x11, x1, #10",
    "  add x12, x1, #11",
    "  add x13, x1, #12",
    "  add x14, x1, #13",
    "  add x15, x1, #14",
    "  add x17, x1, #15",
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

/// The signature wrappers' input offset (`rustc/xmss.rs`, `rustc/sphincs.rs`).
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

const PROT_NONE: i32 = 0;
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const SC_PAGESIZE: i32 = 30;

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: isize) -> *mut u8;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn sysconf(name: i32) -> isize;
}

fn page_size() -> usize {
    let p = unsafe { sysconf(SC_PAGESIZE) };
    if p > 0 { p as usize } else { 4096 }
}

/// Words between `PROT_NONE` guard pages (with leading in-band `GUARD` words up to the page boundary), right-aligned
/// so the end of the payload abuts the trailing `PROT_NONE` guard page: any out-of-bounds read or write past the end
/// faults immediately, and `readonly` areas are protected with `PROT_READ`.
struct Guarded {
    base: *mut u8,
    total: usize,
    page: usize,
    prefix_words: usize,
    len_words: usize,
}

impl Guarded {
    fn with_prot(words: &[u64], readonly: bool) -> Self {
        let page = page_size();
        let payload_bytes = words.len() * 8;
        let min_data = GUARD_WORDS * 8 + payload_bytes;
        let data_bytes = min_data.div_ceil(page).max(1) * page;
        let total = page + data_bytes + page;
        // SAFETY: anonymous private mapping, initially PROT_NONE, then data pages made RW.
        let base = unsafe { mmap(core::ptr::null_mut(), total, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) };
        assert!(base != (!0usize as *mut u8), "mmap failed");
        let data_ptr = unsafe { base.add(page) };
        let rc = unsafe { mprotect(data_ptr, data_bytes, PROT_READ | PROT_WRITE) };
        assert_eq!(rc, 0, "mprotect RW failed");
        let total_words = data_bytes / 8;
        let prefix_words = total_words - words.len();
        let slice = unsafe { core::slice::from_raw_parts_mut(data_ptr as *mut u64, total_words) };
        slice[..prefix_words].fill(GUARD);
        slice[prefix_words..].copy_from_slice(words);
        if readonly {
            let rc = unsafe { mprotect(data_ptr, data_bytes, PROT_READ) };
            assert_eq!(rc, 0, "mprotect RO failed");
        }
        Self {
            base,
            total,
            page,
            prefix_words,
            len_words: words.len(),
        }
    }

    fn new(words: &[u64]) -> Self {
        Self::with_prot(words, false)
    }

    fn new_readonly(words: &[u64]) -> Self {
        Self::with_prot(words, true)
    }

    fn len(&self) -> usize {
        self.len_words
    }

    fn data_words(&self) -> &[u64] {
        unsafe { core::slice::from_raw_parts(self.base.add(self.page) as *const u64, self.prefix_words + self.len_words) }
    }

    fn words(&self) -> &[u64] {
        &self.data_words()[self.prefix_words..]
    }

    /// The inside's address, 8-byte aligned even when empty.
    fn addr(&mut self) -> *mut u64 {
        unsafe { (self.base.add(self.page) as *mut u64).add(self.prefix_words) }
    }

    fn guards_intact(&self) -> bool {
        self.data_words()[..self.prefix_words].iter().all(|&w| w == GUARD)
    }
}

impl Drop for Guarded {
    fn drop(&mut self) {
        unsafe {
            munmap(self.base, self.total);
        }
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
    if let &[rsp_before, rsp_after, rflags] = &regs[SAVED.len()..] {
        if rsp_after != rsp_before {
            faults.push("rsp not preserved".into());
        }
        if rflags & (1 << 10) != 0 {
            faults.push("DF not cleared".into());
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
    let mut words = vec![JUNK; SIG_INPUT_WORD + input.len()];
    words[SIG_INPUT_WORD..SIG_INPUT_WORD + input.len()].copy_from_slice(input);
    let mut ctx = Guarded::new_readonly(&words);
    let mut faults = Vec::new();
    let result = call(verify, ctx.addr(), &mut faults);
    if !ctx.guards_intact() {
        faults.push("a write outside the context".into());
    }
    if ctx.words()[SIG_INPUT_WORD..SIG_INPUT_WORD + input.len()] != *input {
        faults.push("a write to the input".into());
    }
    report(path, expect, result, &faults)
}

/// The read-only context consumed by `leanvm_verify` (`rustc/vm/src/lib.rs`).
const VM_CTX_WORDS: usize = 12;

/// Initialized scratch words, with no reliance on zero-filled memory.
const JUNK: u64 = 0xa5a5_a5a5_a5a5_a5a5;

/// `decoded_words` in `rustc/vm/src/input.rs`: the stream count and elements, then the phases and openings.
fn vm_decoded_words(l: usize) -> usize {
    let opening = 1 + 64 + 4 * 32;
    1 + 2 * (l / 16) + 1 + 8 * (3 + 256 * opening)
}

/// The caller's working-area capacity, bounded by the assertion in `rustc/vm/src/lib.rs`.
const VM_WORK_WORDS: usize = 85438;

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

/// Lays out the 12-word context from `rustc/vm/src/lib.rs`: wire address and byte count (0, 1), bytecode address and
/// word count (2, 3), public input (4..8), decoded address and word count (8, 9), working address and word count
/// (10, 11). Inputs are read-only; scratch starts as `JUNK`. Every area has guard pages.
fn run_vm(path: &str, verify: Verify, expect: u64, bytecode: &[u64], public: &[u64], wire: &[u8]) -> i32 {
    let wire_words = le_words(wire);
    let mut wire_area = Guarded::new_readonly(&wire_words);
    let mut bytecode_area = Guarded::new_readonly(bytecode);
    let mut decoded = Guarded::new(&vec![JUNK; vm_decoded_words(wire.len())]);
    let mut work = Guarded::new(&vec![JUNK; VM_WORK_WORDS]);
    let mut words = [JUNK; VM_CTX_WORDS];
    words[0] = wire_area.addr() as u64;
    words[1] = wire.len() as u64;
    words[2] = bytecode_area.addr() as u64;
    words[3] = bytecode.len() as u64;
    words[4..8].copy_from_slice(public);
    words[8] = decoded.addr() as u64;
    words[9] = decoded.len() as u64;
    words[10] = work.addr() as u64;
    words[11] = work.len() as u64;
    let mut ctx = Guarded::new_readonly(&words);

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
    if ctx.words() != words {
        faults.push("a write to the context".into());
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

/// Defensive context-precondition checks for the rustc-compiled `leanvm_verify` (`rustc/vm/src/lib.rs`).
fn run_vm_preconditions() -> i32 {
    let Some(verify) = VM else {
        eprintln!("harness: leanvm_verify is not linked in");
        return 2;
    };
    let mut wire_area = Guarded::new_readonly(&[0u64; 1]);
    let mut bc_area = Guarded::new_readonly(&[0u64; 24]);
    let mut dec_area = Guarded::new(&vec![JUNK; vm_decoded_words(8)]);
    let mut work_area = Guarded::new(&vec![JUNK; VM_WORK_WORDS]);
    let base: [u64; 12] = [
        wire_area.addr() as u64,
        8,
        bc_area.addr() as u64,
        16,
        0,
        0,
        0,
        0,
        dec_area.addr() as u64,
        dec_area.len() as u64,
        work_area.addr() as u64,
        work_area.len() as u64,
    ];
    let cases: &[(&str, [u64; 12])] = &[
        ("l-ge-2p32", { let mut c = base; c[1] = 1u64 << 32; c }),
        ("n-gt-bcSmall", { let mut c = base; c[3] = ((1u64 << 32) - 10) / 8 + 1; c }),
        ("dec-undersized", { let mut c = base; c[9] = (vm_decoded_words(8) - 1) as u64; c }),
        ("work-undersized", { let mut c = base; c[11] = 1; c }),
        ("dec-null", { let mut c = base; c[8] = 0; c }),
        ("dec-unaligned", { let mut c = base; c[8] += 1; c }),
        ("work-null", { let mut c = base; c[10] = 0; c }),
        ("work-unaligned", { let mut c = base; c[10] += 1; c }),
        ("bc-null-nonzero-n", { let mut c = base; c[2] = 0; c }),
        ("bc-unaligned-nonzero-n", { let mut c = base; c[2] += 1; c }),
        ("wire-null-nonzero-l", { let mut c = base; c[0] = 0; c }),
        ("bc-empty", { let mut c = base; c[3] = 0; c }),
        ("bc-non-pow2", { let mut c = base; c[3] = 24; c }),
    ];
    let mut worst = 0;
    for &(name, header) in cases {
        let mut ctx = Guarded::new_readonly(&header);
        let mut faults = Vec::new();
        let result = call(verify, ctx.addr(), &mut faults);
        if !ctx.guards_intact() {
            faults.push("a write outside the context".into());
        }
        worst = worst.max(report(&format!("vm_precondition_{name}"), 0, result, &faults));
    }
    worst
}

fn main() {
    let cases: Vec<String> = env::args().skip(1).collect();
    if cases.is_empty() {
        eprintln!("usage: harness [--vm-preconditions] CASE...");
        process::exit(2);
    }
    let mut worst = 0;
    for arg in &cases {
        let rc = if arg == "--vm-preconditions" {
            run_vm_preconditions()
        } else {
            run(arg)
        };
        worst = worst.max(rc);
    }
    process::exit(worst);
}
