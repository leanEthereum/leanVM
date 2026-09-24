//! The one-block compression in general-purpose registers.
//!
//! A single hash has only four independent G's per half-round.
//!
//! In vector rows, each link of their chain pays the 2-cycle vector latency of Zen 5.
//!
//! Scalar ALUs take one cycle, and are wide enough to run the four G's side by side.
//!
//! Assembly keeps it scalar: left alone, the compiler vectorizes the unrolled rounds into rows.
//!
//! ```text
//!     v0  eax    v4  r8d    v8   [rsp]        v12  r12d
//!     v1  ecx    v5  r9d    v9   ebp          v13  r13d
//!     v2  edx    v6  r10d   v10  [rsp + 4]    v14  r14d
//!     v3  ebx    v7  r11d   v11  esi          v15  r15d
//! ```
//!
//! The message stays behind `rdi`, which leaves 14 registers for 16 words.
//!
//! The two spilled words are cheap: Zen renames `rsp`-relative memory.

use crate::hash::IV;

/// Message word `w`, as a memory operand.
macro_rules! m {
    ($w:literal) => {
        concat!("dword ptr [rdi + 4*", $w, "]")
    };
}

/// Four independent G functions, emitted one step at a time across all of them.
macro_rules! g {
    ($(($a:literal, $b:literal, $c:literal, $d:literal, $x:literal, $y:literal))*) => {
        concat!(
            $("add ", $a, ", ", m!($x), "\n",)*
            $("add ", $a, ", ", $b, "\n",)*
            $("xor ", $d, ", ", $a, "\n",)*
            $("add ", $a, ", ", m!($y), "\n",)*
            $("ror ", $d, ", 16\n",)*
            $("add ", $c, ", ", $d, "\n",)*
            $("xor ", $b, ", ", $c, "\n",)*
            $("ror ", $b, ", 12\n",)*
            $("add ", $a, ", ", $b, "\n",)*
            $("xor ", $d, ", ", $a, "\n",)*
            $("ror ", $d, ", 8\n",)*
            $("add ", $c, ", ", $d, "\n",)*
            $("xor ", $b, ", ", $c, "\n",)*
            $("ror ", $b, ", 7\n",)*
        )
    };
}

/// One round on the register map above: columns, then diagonals.
macro_rules! round {
    ([$s0:literal, $s1:literal, $s2:literal, $s3:literal, $s4:literal, $s5:literal, $s6:literal, $s7:literal,
      $s8:literal, $s9:literal, $s10:literal, $s11:literal, $s12:literal, $s13:literal, $s14:literal, $s15:literal]) => {
        concat!(
            g!(("eax", "r8d", "dword ptr [rsp]", "r12d", $s0, $s1)(
                "ecx", "r9d", "ebp", "r13d", $s2, $s3
            )("edx", "r10d", "dword ptr [rsp + 4]", "r14d", $s4, $s5)(
                "ebx", "r11d", "esi", "r15d", $s6, $s7
            )),
            g!(("eax", "r9d", "dword ptr [rsp + 4]", "r15d", $s8, $s9)(
                "ecx", "r10d", "esi", "r12d", $s10, $s11
            )("edx", "r11d", "dword ptr [rsp]", "r13d", $s12, $s13)(
                "ebx", "r8d", "ebp", "r14d", $s14, $s15
            )),
        )
    };
}

/// `h[i] ^= v[i] ^ v[i + 8]`, with `h` behind `rdi`.
macro_rules! feed_forward {
    ($($i:literal $vi:literal $vj:literal),*) => {
        concat!($(
            "xor ", $vi, ", ", $vj, "\n",
            "xor ", $vi, ", dword ptr [rdi + 4*", $i, "]\n",
            "mov dword ptr [rdi + 4*", $i, "], ", $vi, "\n",
        )*)
    };
}

/// The BLAKE2s compression on x86-64.
///
/// Out of line, so every caller shares one copy of the kernel.
#[inline(never)]
pub(in crate::hash) fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    // SAFETY: `m` and `h` are valid references.
    //
    // The kernel borrows 32 bytes of stack, and restores `rbx` and `rbp`, which asm cannot name.
    unsafe {
        core::arch::asm!(
            // Stack frame, from `rsp` up:
            //
            //     [rsp]         v8, v10     spilled words
            //     [rsp + 8]     &h          for the feed-forward
            //     [rsp + 16]    rbp, rbx    caller's registers
            "push rbx",
            "push rbp",
            "push rsi",
            "sub rsp, 8",
            // v[0..8] = h.
            "mov eax, dword ptr [rsi]",
            "mov ecx, dword ptr [rsi + 4]",
            "mov edx, dword ptr [rsi + 8]",
            "mov ebx, dword ptr [rsi + 12]",
            "mov r8d, dword ptr [rsi + 16]",
            "mov r9d, dword ptr [rsi + 20]",
            "mov r10d, dword ptr [rsi + 24]",
            "mov r11d, dword ptr [rsi + 28]",
            // v[8..16] = IV, the counter and flag already folded into r12d..r14d.
            "mov dword ptr [rsp], {iv0}",
            "mov ebp, {iv1}",
            "mov dword ptr [rsp + 4], {iv2}",
            "mov esi, {iv3}",
            "mov r15d, {iv7}",
            // The ten rounds.
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
            // h[i] ^= v[i] ^ v[i + 8], through `rdi` now that the message is consumed.
            "mov rdi, qword ptr [rsp + 8]",
            feed_forward!(
                0 "eax" "dword ptr [rsp]", 1 "ecx" "ebp", 2 "edx" "dword ptr [rsp + 4]", 3 "ebx" "esi",
                4 "r8d" "r12d", 5 "r9d" "r13d", 6 "r10d" "r14d", 7 "r11d" "r15d"
            ),
            // Release the frame.
            "add rsp, 16",
            "pop rbp",
            "pop rbx",
            iv0 = const IV[0],
            iv1 = const IV[1],
            iv2 = const IV[2],
            iv3 = const IV[3],
            iv7 = const IV[7],
            inout("rdi") m.as_ptr() => _,
            inout("rsi") h.as_mut_ptr() => _,
            inout("r12d") IV[4] ^ t as u32 => _,
            inout("r13d") IV[5] ^ (t >> 32) as u32 => _,
            inout("r14d") if last { !IV[6] } else { IV[6] } => _,
            out("eax") _, out("ecx") _, out("edx") _,
            out("r8d") _, out("r9d") _, out("r10d") _, out("r11d") _, out("r15d") _,
        );
    }
}
