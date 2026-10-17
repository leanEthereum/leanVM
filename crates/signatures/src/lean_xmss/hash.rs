//! leanXMSS's addresses, on the shared tweakable hash (`crate::tweak`). A chain step's
//! address leaves out the chain index, which follows the value instead
//! (`wots::chain`), so a key's chains share their step addresses.
//!
//! The two layers share one public parameter, so the address separates them: the
//! top layer sets [`TOP`] in `hi`. A bottom address's `lo` is the leaf index, or a
//! node's index `leaf_index >> level`, which also separates the bottom trees; a top
//! address's is the top tree's own.

pub use crate::tweak::*;

use crate::lean_xmss::*;

// Hash types of leanXMSS's own.
/// A node outside a mock key's range.
pub const TWEAK_FILLER: u8 = 13;

/// The top layer's flag in `hi`.
pub const TOP: u32 = 1 << 23;

/// `hi` for `field` on layer `layer` (0 the bottom, 1 the top).
pub fn layer_hi(layer: usize, field: u32) -> u32 {
    field | (layer as u32 * TOP)
}

/// The seed the scheme derives from.
pub fn scheme_seed(seed: &Seed) -> Seed {
    tagged_seed(SEED_TAG, seed)
}
