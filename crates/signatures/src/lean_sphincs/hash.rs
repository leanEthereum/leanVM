//! leanSPHINCS's address types and seed, on the shared tweakable hash
//! (`crate::tweak`), whose address names one hash call in the whole structure.

pub use crate::tweak::*;

use crate::lean_sphincs::*;

// Hash types of leanSPHINCS's own.
pub const TWEAK_ENC: u8 = 4;
/// A pruned key's surrogate siblings.
pub const TWEAK_SURROGATE: u8 = 13;
pub const TWEAK_FOREST_PRF: u8 = 14;
pub const TWEAK_FOREST_CHAIN: u8 = 15;
/// The leaf of a subtree: a small WOTS key's chain tops.
pub const TWEAK_FOREST_KEY_LEAF: u8 = 16;
pub const TWEAK_FOREST_SUBNODE: u8 = 17;
/// The leaf of a tree: the top nodes of its two subtrees.
pub const TWEAK_FOREST_TREE_LEAF: u8 = 18;
pub const TWEAK_FOREST_NODE: u8 = 19;
/// The few-time public key: the top nodes of the trees.
pub const TWEAK_FOREST_KEY: u8 = 20;

/// The seed the scheme derives from.
pub fn scheme_seed(seed: &MasterSecret) -> MasterSecret {
    tagged_seed(SEED_TAG, seed)
}
