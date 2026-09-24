//! Two 16-lane compressions in one hand-scheduled AVX-512 kernel.
//!
//! On Zen 5, a 512-bit add, xor or rotate has a 2-cycle latency.
//!
//! One 16-lane group then waits on its own G chains, and most vector pipes idle.
//!
//! Two groups in lockstep double the independent work, and fill the whole register file:
//!
//! ```text
//!     zmm0  .. zmm15    group A's state
//!     zmm16 .. zmm31    group B's state
//! ```
//!
//! Nothing else fits, so every update is in place and message words stay in memory.
//!
//! The compiler spills at this pressure, hence assembly.

use crate::hash::IV;

/// `op zmmD, zmmD, zmmS`.
macro_rules! rr {
    ($op:literal, $d:literal, $s:literal) => {
        concat!($op, " zmm", $d, ", zmm", $d, ", zmm", $s, "\n")
    };
}

/// `zmmD += m[w]`, with the message word as a memory operand.
macro_rules! addm {
    ($d:literal, $m:literal, $w:literal) => {
        concat!("vpaddd zmm", $d, ", zmm", $d, ", zmmword ptr [", $m, " + 64*", $w, "]\n")
    };
}

/// `zmmD >>>= n`.
macro_rules! ror {
    ($d:literal, $n:literal) => {
        concat!("vprord zmm", $d, ", zmm", $d, ", ", $n, "\n")
    };
}

/// Independent G functions, emitted one step at a time across all of them.
///
/// Each step is then a run of independent instructions.
///
/// The second message add is hoisted early, off the dependency chain.
macro_rules! g {
    ($(($a:literal, $b:literal, $c:literal, $d:literal, $m:literal, $x:literal, $y:literal))*) => {
        concat!(
            $(addm!($a, $m, $x),)*
            $(rr!("vpaddd", $a, $b),)*
            $(rr!("vpxord", $d, $a),)*
            $(addm!($a, $m, $y),)*
            $(ror!($d, 16),)*
            $(rr!("vpaddd", $c, $d),)*
            $(rr!("vpxord", $b, $c),)*
            $(ror!($b, 12),)*
            $(rr!("vpaddd", $a, $b),)*
            $(rr!("vpxord", $d, $a),)*
            $(ror!($d, 8),)*
            $(rr!("vpaddd", $c, $d),)*
            $(rr!("vpxord", $b, $c),)*
            $(ror!($b, 7),)*
        )
    };
}

/// One round of both groups: columns, then diagonals.
#[rustfmt::skip]
macro_rules! round {
    ([$s0:literal, $s1:literal, $s2:literal, $s3:literal, $s4:literal, $s5:literal, $s6:literal, $s7:literal,
      $s8:literal, $s9:literal, $s10:literal, $s11:literal, $s12:literal, $s13:literal, $s14:literal, $s15:literal]) => {
        concat!(
            g!(
                (0, 4, 8, 12, "{ma}", $s0, $s1)       (1, 5, 9, 13, "{ma}", $s2, $s3)
                (2, 6, 10, 14, "{ma}", $s4, $s5)      (3, 7, 11, 15, "{ma}", $s6, $s7)
                (16, 20, 24, 28, "{mb}", $s0, $s1)    (17, 21, 25, 29, "{mb}", $s2, $s3)
                (18, 22, 26, 30, "{mb}", $s4, $s5)    (19, 23, 27, 31, "{mb}", $s6, $s7)
            ),
            g!(
                (0, 5, 10, 15, "{ma}", $s8, $s9)      (1, 6, 11, 12, "{ma}", $s10, $s11)
                (2, 7, 8, 13, "{ma}", $s12, $s13)     (3, 4, 9, 14, "{ma}", $s14, $s15)
                (16, 21, 26, 31, "{mb}", $s8, $s9)    (17, 22, 27, 28, "{mb}", $s10, $s11)
                (18, 23, 24, 29, "{mb}", $s12, $s13)  (19, 20, 25, 30, "{mb}", $s14, $s15)
            ),
        )
    };
}

/// Load `v[i] = h[i]` and broadcast `v[8 + i]` from `src`, for both groups.
macro_rules! init {
    ($($i:literal $j:literal $vi:literal $vj:literal $src:literal),*) => {
        concat!($(
            "vmovdqu64 zmm", $i, ", zmmword ptr [{h} + 64*", $i, "]\n",
            "vmovdqu64 zmm", $j, ", zmmword ptr [{h} + 512 + 64*", $i, "]\n",
            "vpbroadcastd zmm", $vi, ", ", $src, "\n",
            "vmovdqa64 zmm", $vj, ", zmm", $vi, "\n",
        )*)
    };
}

/// `h[i] ^= v[i] ^ v[i + 8]` for both groups.
///
/// One `vpternlogd` each: `0x96` is the three-way xor.
macro_rules! feed_forward {
    ($($i:literal $j:literal $vi:literal $vj:literal),*) => {
        concat!($(
            "vpternlogd zmm", $i, ", zmm", $vi, ", zmmword ptr [{h} + 64*", $i, "], 0x96\n",
            "vmovdqu64 zmmword ptr [{h} + 64*", $i, "], zmm", $i, "\n",
            "vpternlogd zmm", $j, ", zmm", $vj, ", zmmword ptr [{h} + 512 + 64*", $i, "], 0x96\n",
            "vmovdqu64 zmmword ptr [{h} + 512 + 64*", $i, "], zmm", $j, "\n",
        )*)
    };
}

/// Compress two transposed 16-lane blocks at byte counter `t`.
///
/// Both chaining values are updated in place:
///
/// ```text
///     byte 64 * i          group A's word i
///     byte 512 + 64 * i    group B's word i
/// ```
///
/// The counter and final flag arrive in registers, so no per-block row round-trips through memory.
///
/// # Safety
///
/// - `h` must be valid for reads and writes of `2 * 8 * 16` `u32`.
/// - `ma` and `mb` must each be valid for reads of `16 * 16` `u32`.
#[inline(always)]
pub(super) unsafe fn compress_x2(h: *mut u32, ma: *const u32, mb: *const u32, t: u64, last: bool) {
    let iv: &'static [u32; 8] = &IV;
    // SAFETY: the caller guarantees the three buffers.
    // The kernel touches no stack and no memory other than theirs and `IV`.
    unsafe {
        core::arch::asm!(
            // v[0..8] = h, and v[8..16] = the IV row with the counter and flag folded in.
            init!(
                0 16 8 24 "dword ptr [{iv}]",
                1 17 9 25 "dword ptr [{iv} + 4]",
                2 18 10 26 "dword ptr [{iv} + 8]",
                3 19 11 27 "dword ptr [{iv} + 12]",
                4 20 12 28 "{t0:e}",
                5 21 13 29 "{t1:e}",
                6 22 14 30 "{f:e}",
                7 23 15 31 "dword ptr [{iv} + 28]"
            ),
            // The ten rounds (RFC 7693 message schedule), both groups in lockstep.
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
            // h[i] ^= v[i] ^ v[i + 8], written back in place.
            feed_forward!(
                0 16 8 24, 1 17 9 25, 2 18 10 26, 3 19 11 27, 4 20 12 28, 5 21 13 29, 6 22 14 30, 7 23 15 31
            ),
            h = in(reg) h,
            ma = in(reg) ma,
            mb = in(reg) mb,
            iv = in(reg) iv.as_ptr(),
            t0 = in(reg) iv[4] ^ t as u32,
            t1 = in(reg) iv[5] ^ (t >> 32) as u32,
            f = in(reg) if last { !iv[6] } else { iv[6] },
            out("zmm0") _, out("zmm1") _, out("zmm2") _, out("zmm3") _,
            out("zmm4") _, out("zmm5") _, out("zmm6") _, out("zmm7") _,
            out("zmm8") _, out("zmm9") _, out("zmm10") _, out("zmm11") _,
            out("zmm12") _, out("zmm13") _, out("zmm14") _, out("zmm15") _,
            out("zmm16") _, out("zmm17") _, out("zmm18") _, out("zmm19") _,
            out("zmm20") _, out("zmm21") _, out("zmm22") _, out("zmm23") _,
            out("zmm24") _, out("zmm25") _, out("zmm26") _, out("zmm27") _,
            out("zmm28") _, out("zmm29") _, out("zmm30") _, out("zmm31") _,
            options(nostack),
        );
    }
}
