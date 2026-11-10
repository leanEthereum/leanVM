//! The ISA and the `DEREF` store modes.

use primitives::field::{F64, F128};

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
        /// The immediate stored into `mem[fp·o]`. A full 128-bit machine word
        /// (`E = F128`); K-valued constants (addresses, small ints) ride the
        /// low lane with `c1 = 0`.
        k: F128,
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
    /// read in the layout `in_odd` names and written to consecutive cells from `out` in the layout
    /// `out_odd` names ([`crate::keccak::cell_lanes`]): the first `out_cells` of the thirteen output
    /// cells, the others left untouched. The cells read are four
    /// independently addressed cells `m`, four consecutive cells from `tail`, the cell `b8`, and
    /// four consecutive cells from `cap` (the capacity lanes 17..25).
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
        out_cells: OutCells,
    },
}

/// How many of a `KECCAK`'s thirteen output cells it writes, from `out` on: the first, the first two (a
/// 256-bit digest), or all thirteen (a state a later block reads). Two bytecode flags carry the choice, so the
/// program fixes it, never the prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutCells {
    One,
    Two,
    All,
}

impl OutCells {
    /// The cells written.
    pub const fn cells(self) -> usize {
        match self {
            Self::One => 1,
            Self::Two => 2,
            Self::All => crate::keccak::STATE_CELLS,
        }
    }

    /// The bytecode flags: whether output cell 1 is written, and whether cells `2..13` are.
    pub(crate) const fn flags(self) -> (bool, bool) {
        (!matches!(self, Self::One), matches!(self, Self::All))
    }
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
