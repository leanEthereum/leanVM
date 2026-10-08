//! One compression with its state in general-purpose registers.
//!
//! The compiler spills a 16-word state over 15 free registers, and reloads the message pointer.
//!
//! Here the message is copied to the stack and read at `rsp` offsets, which frees its pointer.
//!
//! Fifteen words then live in registers, and `v[11]` on the stack:
//!
//! ```text
//!     v[0..4]     eax  ecx  edx  esi
//!     v[4..8]     edi  r8d  r9d  r10d
//!     v[8..12]    r11d r12d r13d [rsp + 64]
//!     v[12..16]   r14d r15d ebx  ebp
//! ```
//!
//! `v[11]` is always a G's `c`, whose partners are registers, so no instruction takes two memory operands.

use crate::hash::IV;

/// The stack slot holding `v[11]`.
macro_rules! v11 {
    () => {
        "dword ptr [rsp + 64]"
    };
}

/// Four independent G functions, emitted one step at a time across all of them.
///
/// Each G is `(a, b, c, d, x, y)`: four state registers and two message word indices.
macro_rules! g {
    ($(($a:expr, $b:expr, $c:expr, $d:expr, $x:literal, $y:literal))*) => {
        concat!(
            $("add ", $a, ", dword ptr [rsp + 4*", $x, "]\n",)*
            $("add ", $a, ", ", $b, "\n",)*
            $("xor ", $d, ", ", $a, "\n",)*
            $("ror ", $d, ", 16\n",)*
            $("add ", $c, ", ", $d, "\n",)*
            $("xor ", $b, ", ", $c, "\n",)*
            $("ror ", $b, ", 12\n",)*
            $("add ", $a, ", dword ptr [rsp + 4*", $y, "]\n",)*
            $("add ", $a, ", ", $b, "\n",)*
            $("xor ", $d, ", ", $a, "\n",)*
            $("ror ", $d, ", 8\n",)*
            $("add ", $c, ", ", $d, "\n",)*
            $("xor ", $b, ", ", $c, "\n",)*
            $("ror ", $b, ", 7\n",)*
        )
    };
}

/// One round with the message schedule `s`: columns, then diagonals.
#[rustfmt::skip]
macro_rules! round {
    ([$s0:literal, $s1:literal, $s2:literal, $s3:literal, $s4:literal, $s5:literal, $s6:literal, $s7:literal,
      $s8:literal, $s9:literal, $s10:literal, $s11:literal, $s12:literal, $s13:literal, $s14:literal, $s15:literal]) => {
        concat!(
            g!(
                ("eax", "edi", "r11d", "r14d", $s0, $s1)
                ("ecx", "r8d", "r12d", "r15d", $s2, $s3)
                ("edx", "r9d", "r13d", "ebx", $s4, $s5)
                ("esi", "r10d", v11!(), "ebp", $s6, $s7)
            ),
            g!(
                ("eax", "r8d", "r13d", "ebp", $s8, $s9)
                ("ecx", "r9d", v11!(), "r14d", $s10, $s11)
                ("edx", "r10d", "r11d", "r15d", $s12, $s13)
                ("esi", "edi", "r12d", "ebx", $s14, $s15)
            ),
        )
    };
}

/// The BLAKE2s compression: absorb block `m` at byte counter `t` into `h`.
///
/// Equal to the portable compression, which the tests pin it to.
#[inline]
pub(in crate::hash) fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    // SAFETY: `h` and `m` are valid for their 32 and 64 bytes.
    // The kernel saves and restores `rbx` and `rbp`, and frees the 88 bytes of stack it takes.
    unsafe {
        core::arch::asm!(
            "push rbx",
            "push rbp",
            "sub rsp, 88",
            // The message to `rsp + 0 .. 64`, and `h`'s address to `rsp + 72`.
            //
            // General-purpose moves: no vector register, so no SSE and AVX transition.
            "mov rax, [rsi]",
            "mov rcx, [rsi + 8]",
            "mov rdx, [rsi + 16]",
            "mov r8, [rsi + 24]",
            "mov [rsp], rax",
            "mov [rsp + 8], rcx",
            "mov [rsp + 16], rdx",
            "mov [rsp + 24], r8",
            "mov rax, [rsi + 32]",
            "mov rcx, [rsi + 40]",
            "mov rdx, [rsi + 48]",
            "mov r8, [rsi + 56]",
            "mov [rsp + 32], rax",
            "mov [rsp + 40], rcx",
            "mov [rsp + 48], rdx",
            "mov [rsp + 56], r8",
            "mov [rsp + 72], rdi",
            // v[0..8] = h, and v[8..16] = the IV with the counter and flag folded in.
            "mov ebx, r13d",
            "mov eax, [rdi]",
            "mov ecx, [rdi + 4]",
            "mov edx, [rdi + 8]",
            "mov esi, [rdi + 12]",
            "mov r8d, [rdi + 20]",
            "mov r9d, [rdi + 24]",
            "mov r10d, [rdi + 28]",
            "mov edi, [rdi + 16]",
            "mov r11d, {iv0}",
            "mov r12d, {iv1}",
            "mov r13d, {iv2}",
            concat!("mov ", v11!(), ", {iv3}"),
            "mov ebp, {iv7}",
            // The ten rounds (RFC 7693 message schedule).
            round!([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
            round!([14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]),
            round!([11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4]),
            round!([7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8]),
            round!([9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13]),
            round!([2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9]),
            round!([12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]),
            round!([13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10]),
            round!([6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5]),
            round!([10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]),
            // h[i] ^= v[i] ^ v[i + 8], through `h`'s address back in `rdi`.
            "xor edi, r14d",
            "mov [rsp + 80], edi",
            "mov rdi, [rsp + 72]",
            "xor eax, r11d",
            "xor [rdi], eax",
            "xor ecx, r12d",
            "xor [rdi + 4], ecx",
            "xor edx, r13d",
            "xor [rdi + 8], edx",
            concat!("xor esi, ", v11!()),
            "xor [rdi + 12], esi",
            "mov eax, [rsp + 80]",
            "xor [rdi + 16], eax",
            "xor r8d, r15d",
            "xor [rdi + 20], r8d",
            "xor r9d, ebx",
            "xor [rdi + 24], r9d",
            "xor r10d, ebp",
            "xor [rdi + 28], r10d",
            "add rsp, 88",
            "pop rbp",
            "pop rbx",
            iv0 = const IV[0],
            iv1 = const IV[1],
            iv2 = const IV[2],
            iv3 = const IV[3],
            iv7 = const IV[7],
            inout("rdi") h.as_mut_ptr() => _,
            inout("rsi") m.as_ptr() => _,
            inout("r13") if last { !IV[6] } else { IV[6] } => _,
            inout("r14") IV[4] ^ t as u32 => _,
            inout("r15") IV[5] ^ (t >> 32) as u32 => _,
            out("rax") _, out("rcx") _, out("rdx") _,
            out("r8") _, out("r9") _, out("r10") _, out("r11") _, out("r12") _,
        );
    }
}
