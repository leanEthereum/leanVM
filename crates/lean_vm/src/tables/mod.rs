mod extension_op;
pub use extension_op::*;

mod poseidon;
pub use poseidon::*;

mod poseidon_24;
pub use poseidon_24::*;

mod table_enum;
pub use table_enum::*;

mod table_trait;
pub use table_trait::*;

mod execution;
pub use execution::*;

mod utils;
pub(crate) use utils::*;

// In logup interractions, the `domainsep` is the last entry of every tuple going into
// the bus. It separates the precompile tables from each other and — since every value
// avoids the reserved memory (1) and bytecode (2) domainseps — also from the memory and
// bytecode lookups.
//
//   Poseidon16  (odd >= 3):  3 + 2·flag_permute + 4·flag_short + 8·flag_left + 16·flag_left·offset_left
//   ExtensionOp (0 mod 4):   4·flag_be + 8·flag_add + 16·flag_dot_product + 32·flag_eq + 64·len
//   Poseidon24  (2 mod 4, >2): 6 + 4·mode  (Compress0_9=6, Permute0_9=10, Permute9_18=14)
//
