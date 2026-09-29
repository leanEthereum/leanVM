//! The one-block compression in general-purpose registers.
//!
//! A single hash has only four independent G's per half-round.
//!
//! In NEON rows, each link of their chain pays the 2-cycle vector latency.
//!
//! Scalar ALUs take one cycle, and are wide enough to run the four G's side by side.
//!
//! Assembly fixes the order, one step at a time across all four G's.
//!
//! The compiler's own schedule of the unrolled rounds measured slower.
//!
//! ```text
//!     v0..v15    w0..w15
//!     message    behind x17, two words per G in w20..w27
//! ```

use crate::hash::IV;

/// Load message word `w` into register `r`.
macro_rules! ldm {
    ($r:literal, $w:literal) => {
        concat!("ldr ", $r, ", [x17, #4*", $w, "]\n")
    };
}

/// Four independent G functions, emitted one step at a time across all of them.
///
/// Each message word is added to `a` before `b` is, so it stays off the chain.
///
/// The second one comes late, just before it is needed.
///
/// Issued early, it takes an ALU slot from the chain.
macro_rules! g {
    ($(($a:literal, $b:literal, $c:literal, $d:literal, $mx:literal, $my:literal, $x:literal, $y:literal))*) => {
        concat!(
            $(ldm!($mx, $x), ldm!($my, $y),)*
            $("add ", $a, ", ", $a, ", ", $mx, "\n",)*
            $("add ", $a, ", ", $a, ", ", $b, "\n",)*
            $("eor ", $d, ", ", $d, ", ", $a, "\n",)*
            $("ror ", $d, ", ", $d, ", #16\n",)*
            $("add ", $c, ", ", $c, ", ", $d, "\n",)*
            $("eor ", $b, ", ", $b, ", ", $c, "\n",)*
            $("add ", $a, ", ", $a, ", ", $my, "\n",)*
            $("ror ", $b, ", ", $b, ", #12\n",)*
            $("add ", $a, ", ", $a, ", ", $b, "\n",)*
            $("eor ", $d, ", ", $d, ", ", $a, "\n",)*
            $("ror ", $d, ", ", $d, ", #8\n",)*
            $("add ", $c, ", ", $c, ", ", $d, "\n",)*
            $("eor ", $b, ", ", $b, ", ", $c, "\n",)*
            $("ror ", $b, ", ", $b, ", #7\n",)*
        )
    };
}

/// One round on the register map above: columns, then diagonals.
macro_rules! round {
    ([$s0:literal, $s1:literal, $s2:literal, $s3:literal, $s4:literal, $s5:literal, $s6:literal, $s7:literal,
      $s8:literal, $s9:literal, $s10:literal, $s11:literal, $s12:literal, $s13:literal, $s14:literal, $s15:literal]) => {
        concat!(
            g!(("w0", "w4", "w8", "w12", "w20", "w21", $s0, $s1)(
                "w1", "w5", "w9", "w13", "w22", "w23", $s2, $s3
            )("w2", "w6", "w10", "w14", "w24", "w25", $s4, $s5)(
                "w3", "w7", "w11", "w15", "w26", "w27", $s6, $s7
            )),
            g!(("w0", "w5", "w10", "w15", "w20", "w21", $s8, $s9)(
                "w1", "w6", "w11", "w12", "w22", "w23", $s10, $s11
            )("w2", "w7", "w8", "w13", "w24", "w25", $s12, $s13)(
                "w3", "w4", "w9", "w14", "w26", "w27", $s14, $s15
            )),
        )
    };
}

/// The BLAKE2s compression on aarch64.
///
/// Out of line, so every caller shares one copy of the kernel.
#[inline(never)]
pub(in crate::hash) fn compress(h: &mut [u32; 8], m: &[u32; 16], t: u64, last: bool) {
    // v[0..8] = h.
    let [mut v0, mut v1, mut v2, mut v3, mut v4, mut v5, mut v6, mut v7] = *h;
    // v[8..16] = IV, with the counter and final flag folded into v12..v14.
    let [mut v8, mut v9, mut v10, mut v11] = [IV[0], IV[1], IV[2], IV[3]];
    let mut v12 = IV[4] ^ t as u32;
    let mut v13 = IV[5] ^ (t >> 32) as u32;
    let mut v14 = IV[6] ^ (last as u32).wrapping_neg();
    let mut v15 = IV[7];
    // SAFETY: `m` is a valid reference to 64 readable bytes.
    //
    // The kernel reads only `m`, and writes only the registers it names.
    unsafe {
        core::arch::asm!(
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
            in("x17") m.as_ptr(),
            inout("w0") v0, inout("w1") v1, inout("w2") v2, inout("w3") v3,
            inout("w4") v4, inout("w5") v5, inout("w6") v6, inout("w7") v7,
            inout("w8") v8, inout("w9") v9, inout("w10") v10, inout("w11") v11,
            inout("w12") v12, inout("w13") v13, inout("w14") v14, inout("w15") v15,
            out("w20") _, out("w21") _, out("w22") _, out("w23") _,
            out("w24") _, out("w25") _, out("w26") _, out("w27") _,
            options(pure, readonly, nostack, preserves_flags),
        );
    }
    // Feed-forward: h[i] ^= v[i] ^ v[i + 8].
    let v = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15];
    for (i, hi) in h.iter_mut().enumerate() {
        *hi ^= v[i] ^ v[i + 8];
    }
}
