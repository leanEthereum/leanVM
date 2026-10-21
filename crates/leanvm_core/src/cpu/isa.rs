//! The ISA and the `DEREF` store modes.

use primitives::field::{F64, F192};

#[derive(Clone, Copy, Debug)]
pub enum Op {
    Xor {
        a: u32,
        b: u32,
        c: u32,
    },
    Mul {
        a: u32,
        b: u32,
        c: u32,
    },
    Set {
        o: u32,
        /// The immediate stored into `mem[fp·o]`. A full 192-bit machine word
        /// (`E = F192`); K-valued constants (addresses, small ints) ride the
        /// low lane with `c1 = c2 = 0`.
        k: F192,
    },
    Deref {
        o1: u32,
        o2: u32,
        o3: u32,
        mode: DerefMode,
    },
    Jump {
        oc: u32,
        od: u32,
        of: u32,
    },
    /// `KECCAK`: the Keccak-f\[1600\] permutation of a 25-lane state held in thirteen cells,
    /// read in the layout `in_odd` names and written to thirteen consecutive cells from `out` in
    /// the layout `out_odd` names ([`crate::keccak::cell_lanes`]). The cells read are four
    /// independently addressed cells `m`, four consecutive cells from `tail`, the cell `b8`, and
    /// four consecutive cells from `cap` (the capacity lanes 17..25), each canonical (top limb
    /// zero).
    ///
    /// A program absorbs a 136-byte block by XORing its nine message cells into the previous
    /// output: block `k` of a message laid out in cells starts at cell `17k / 2`, halfway
    /// through it when `k` is odd, and the odd layout pairs the lanes as such a block's cells
    /// do. The relation is proven by the Keccak reduction ([`crate::keccak`]).
    Keccak {
        m: [u32; 4],
        tail: u32,
        b8: u32,
        cap: u32,
        out: u32,
        in_odd: bool,
        out_odd: bool,
    },
}

/// The source `DEREF` stores at `mem[loc_o1·o2]`: a local cell, the return
/// address `g²·pc`, or the frame pointer. Encoded as two boolean flags `(f_pc,
/// f_fp)`: `Cell=(0,0)`, `Pc=(1,0)`, `Fp=(0,1)`, keeping the store constraint degree 2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerefMode {
    Cell,
    Pc,
    Fp,
}

impl DerefMode {
    pub(crate) fn f_pc(self) -> F64 {
        if self == DerefMode::Pc { F64::ONE } else { F64::ZERO }
    }
    pub(crate) fn f_fp(self) -> F64 {
        if self == DerefMode::Fp { F64::ONE } else { F64::ZERO }
    }
}
