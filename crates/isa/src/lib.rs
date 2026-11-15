//! The leanVM instruction set, shared by the zkDSL compiler, which emits it, and both provers, which execute and prove
//! it: the opcodes ([`Op`]), the hints a compiled program carries for its prover ([`RHint`]), the program as the
//! compiler hands it over ([`CompiledProgram`]) and as the provers prove it ([`Program`]). Machine words are the
//! verifier's field elements. A prover of these programs is a [`Prover`], what the crates both provers share run on.
//! And the counts they print, grouped by [`pretty_integer`] and [`pretty_f64`].

mod pretty;
mod program;
mod prover;

pub use pretty::{pretty_f64, pretty_integer};
pub use program::{BytecodeColumns, Program};
pub use prover::{Prover, Stats};
use std::collections::HashMap;
use verifier::{E, K};

/// Cells a sponge state occupies.
pub const STATE_CELLS: usize = 13;
/// The rate cells of a state, the nine a block of a message laid out in cells covers.
pub const RATE_CELLS: usize = 9;

/// Frame-relative offset operand.
pub type Off = u32;

/// A compiled program: the bytecode, a power of two long, and what its prover needs besides.
#[derive(Clone, Debug)]
pub struct CompiledProgram {
    pub prog: Vec<Op>,
    /// Allocation and advice hints, keyed by global pc: the nondeterminism an execution needs.
    pub hints: HashMap<u32, Vec<RHint>>,
    /// The size of `main`'s frame.
    pub main_frame: u32,
    /// Function pc-ranges `(name, entry, len)`, for profiles and failure reports.
    pub fn_ranges: Vec<(String, u32, u32)>,
    /// Source line of the statement that emitted each pc, shorter than `prog`, which is padded.
    pub src_lines: Vec<u32>,
}

impl CompiledProgram {
    /// Instructions before the pad to a power of two: the compiled functions, or the whole bytecode of a
    /// hand-assembled program.
    pub fn code_len(&self) -> usize {
        match self.fn_ranges.as_slice() {
            [] => self.prog.len(),
            ranges => ranges.iter().map(|&(_, _, len)| len as usize).sum(),
        }
    }

    /// Where `pc` came from: `"verify_sub (line 2204)"` when the compiler left a line for it, the function name alone
    /// otherwise (a hand-assembled program, or padding). A run-time failure reports it.
    pub fn site_at(&self, pc: u32) -> String {
        match self.src_lines.get(pc as usize) {
            Some(&line) if line != 0 => format!("{} (line {line})", self.fn_at(pc)),
            _ => self.fn_at(pc).to_string(),
        }
    }

    /// The compiled function containing `pc`.
    fn fn_at(&self, pc: u32) -> &str {
        self.fn_ranges
            .iter()
            .find(|(_, entry, len)| pc >= *entry && pc < *entry + *len)
            .map_or("<unknown fn>", |(name, _, _)| name.as_str())
    }
}

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
        /// (`E`); K-valued constants (addresses, small ints) ride the
        /// low lane with `c1 = 0`.
        k: E,
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
    /// `out_odd` names (`verifier::layout::keccak_cell_lanes`): the first `out_cells` of the thirteen output
    /// cells, the others left untouched. The cells read are four
    /// independently addressed cells `m`, four consecutive cells from `tail`, the cell `b8`, and
    /// four consecutive cells from `cap` (the capacity lanes 17..25).
    ///
    /// A program absorbs a 136-byte block by XORing its nine message cells into the previous
    /// output: block `k` of a message laid out in cells starts at cell `17k / 2`, halfway
    /// through it when `k` is odd, and the odd layout pairs the lanes as such a block's cells
    /// do. Each prover proves the relation by its Keccak reduction.
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
            Self::All => STATE_CELLS,
        }
    }

    /// The bytecode flags: whether output cell 1 is written, and whether cells `2..13` are.
    pub const fn flags(self) -> (bool, bool) {
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
    /// The `f_pc` flag.
    pub const fn f_pc(self) -> bool {
        matches!(self, Self::Pc)
    }

    /// The `f_fp` flag.
    pub const fn f_fp(self) -> bool {
        matches!(self, Self::Fp)
    }
}

/// Where a computed-advice bit buffer lives. Frame cells are ordinary memory, so
/// a run of them serves as well as a heap region and costs no `DEREF` to index at
/// a compile-time offset; the heap form stays for a buffer indexed at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitsDest {
    /// Frame cells `fp+base+k`.
    Stack(Off),
    /// Heap cells `m[fp+ptr]·g^k`, the pointer read at run time.
    Heap(Off),
}

/// A hint resolved to concrete offsets/sizes, keyed by global program counter.
#[derive(Clone, Debug)]
pub enum RHint {
    /// Announce a pointer into a reserved run of frames.
    FrameAddress { offset: Off },
    /// Reserve `log_g(m[end] * start_inverse)` consecutive frames of `size` cells,
    /// then the `tail` cells the final, untaken call writes of one more.
    AllocFrames {
        ptr: Off,
        size: u32,
        end: Off,
        start_inverse: K,
        tail: u32,
    },
    /// Allocate a fresh region of `size` cells and write `g^{base}` to the cell.
    Alloc { ptr: Off, size: u32 },
    /// `Alloc` with the cell count read at runtime as the g-power exponent of
    /// `m[fp+size]`.
    AllocDyn { ptr: Off, size: Off },
    /// Pop stream `name`'s next entry (`len` values) into frame cells `fp+base+k`.
    WitnessStack { name: String, base: Off, len: u32 },
    /// Pop stream `name`'s next entry (`len` values) into heap cells `m[fp+ptr]·g^{lo+k}`.
    WitnessHeap { name: String, ptr: Off, lo: u32, len: u32 },
    /// Write `g^max(log2_ceil(value), floor)` into `fp+dst`, where `value` is the
    /// integer reconstructed from the `nbits` bits at `bits`.
    Log2Ceil {
        bits: BitsDest,
        dst: Off,
        nbits: u32,
        floor: u32,
    },
    /// Write the low `nbits` bits of `m[fp+value]` into `bits`.
    BitDecompose { value: Off, bits: BitsDest, nbits: u32 },
    /// Write the `nbits` bits of `n`, where `m[fp+value] = g^n` (a bounded
    /// discrete log at witness generation), into `bits`.
    BitDecomposeExp { value: Off, bits: BitsDest, nbits: u32 },
    /// Write `g^d_j` for the `ndigits` base-`2^digit_bits` digits `d_j` of `n >> s` into
    /// `dst`, where `m[fp+value] = g^n` with `n < 2^nbits` and `s` is `start` or, given
    /// `start_cell`, the exponent of `m[fp+start_cell]`.
    DigitDecomposeExp {
        value: Off,
        dst: BitsDest,
        nbits: u32,
        ndigits: u32,
        digit_bits: u32,
        start: u32,
        start_cell: Option<Off>,
    },
    /// Write `count` windows of `width` bits of `m[fp+value]`, from bit `start` on, into
    /// `dest` from cell `at` on, as g-powers: window `i` is `g^n` for `n` its bits read as an integer.
    WindowsExp {
        value: Off,
        dest: BitsDest,
        at: u32,
        start: u32,
        width: u32,
        count: u32,
    },
    /// Write the first `len` K-coordinate limbs of `m[fp+value]` to
    /// `m[fp+base..]`. Computed advice; callers constrain the result.
    FieldLimbs { value: Off, base: Off, len: u32 },
    /// Write `m[fp+value]⁻¹` to `m[fp+dst]`, or `0` when the value is zero.
    /// Untrusted: `assert a != b` multiplies the two back together and asserts
    /// `1`, which a zero value cannot satisfy (`FnLower::lower_assert_ne`).
    Inverse { value: Off, dst: Off },
    /// Prover-side debug print (`print(...)` in the zkDSL): display the value
    /// of `m[fp+cell]` at this program point. Witness generation only.
    Print { label: String, cell: Off },
}
