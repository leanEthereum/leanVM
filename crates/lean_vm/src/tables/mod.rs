mod extension_op;
pub use extension_op::*;

mod poseidon;
pub use poseidon::*;

mod table_enum;
pub use table_enum::*;

mod table_trait;
pub use table_trait::*;

mod execution;
pub use execution::*;

mod utils;
pub(crate) use utils::*;

// In logup interractions, the `domainsep` is the last entry of every tuple going into
// the bus. It separates the two precompile tables from each other (Poseidon16 is odd,
// ExtensionOp is a multiple of 4), and — since every value is odd `>= 3` (Poseidon16) or
// a multiple of 4 (ExtensionOp) — also from the memory and bytecode lookups, whose
// reserved domainseps are respectively 1 and 2.
//
//   Poseidon16  (odd >= 3): 3 + 2·flag_permute + 4·flag_half + 8·flag_left + 16·flag_left·offset_left
//   ExtensionOp (0 mod 4):  4·is_be + 8·flag_add + 16·flag_mul + 32·flag_poly_eq + 64·len
//
