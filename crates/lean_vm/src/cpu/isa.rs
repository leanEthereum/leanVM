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
    /// `BLAKE2s`: one standard BLAKE2s compression. The four 16-byte
    /// message chunks `ins` (each a canonical 128-bit chunk in ONE 192-bit cell,
    /// top limb zero) form the 64-byte block; the digest lands in the TWO
    /// consecutive cells `out, out+1`. Each message chunk is addressed
    /// independently, with no forced contiguity, so the caller need not assemble
    /// its operands into adjacent cells. Every operand is a memory operand, the
    /// metadata included. The compression relation is proven by flock.
    Blake2s {
        ins: [u32; 4],
        /// Base of two consecutive cells holding the 256-bit chaining value
        /// (canonical 128-bit chunks, top limbs zero).
        cv: u32,
        out: u32,
        /// The cell holding the metadata `counter:u64 | f0:u32 | f1:u32`,
        /// little-endian in its two low K-lanes (top lane zero, as for every
        /// other cell this opcode reads). `f0` is the final-block flag and `f1`
        /// the last-node flag. A memory operand like the rest, so a program can
        /// hash any length: a compile-time counter is one pooled `SET` per
        /// frame, a runtime one any cell the program computes.
        md: u32,
    },
    /// `SHA3`: one step of the cell sponge ([`primitives::keccak::step`]):
    /// Keccak-f of a 25-lane state after XORing the padding's last bit into lane
    /// 16. The state is read from thirteen canonical cells (two lanes each, top
    /// limb zero) and the result written to thirteen, both in the order of
    /// [`crate::hash_flock_keccak::CELL_LANES`]: eight independently addressed cells `m`
    /// (lanes 0..16, the 128 bytes of a block), and five consecutive cells from `cap`
    /// (lane 16 alone, its high lane zero, then the capacity lanes 17..25). A
    /// `digest` step writes the first two output cells alone: the digest.
    ///
    /// A fresh hash reads a zero `cap`; a later block reads the previous output's
    /// last five cells there, and XORs its message into the previous output's
    /// first eight to form `m`. The relation is proven by flock.
    Sha3 {
        m: [u32; 8],
        cap: u32,
        out: u32,
        digest: bool,
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
