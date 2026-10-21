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
    /// `KECCAK`: one step of the cell sponge ([`primitives::hash::step`]):
    /// Keccak-f of a 25-lane state after XORing the padding's last bit into lane
    /// 16. The state is read from thirteen canonical cells (two lanes each, top
    /// limb zero) and the result written to thirteen, both in the order of
    /// [`crate::keccak::CELL_LANES`]: four independently addressed cells `m`
    /// (lanes 0..8, the first 64 bytes of a block), four consecutive cells from
    /// `tail` (lanes 8..16, the other 64), and five consecutive cells from `cap`
    /// (lane 16 alone, its high lane zero, then the capacity lanes 17..25).
    ///
    /// A fresh hash reads a zero `cap`; a later block reads the previous output's
    /// last five cells there, and XORs its message into the previous output's
    /// first eight to form `m` and `tail`. The relation is proven by the Keccak
    /// reduction ([`crate::keccak`]).
    Keccak {
        m: [u32; 4],
        tail: u32,
        cap: u32,
        out: u32,
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
