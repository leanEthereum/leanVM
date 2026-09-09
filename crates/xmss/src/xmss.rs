//! XMSS: a Merkle tree of `2^LOG_LIFETIME` WOTS public-key hashes.
//!
//! For a range of R = epoch_end -
//! epoch_start + 1 epochs, storage is O(sqrt(R) + LOG_LIFETIME) instead of O(R).
//! The key stores the top tree (in-range band plus a thin spine) and one cached
//! bottom subtree, cut at `split_level = ceil(log2(R)) / 2`. Out-of-range nodes
//! are deterministic `gen_random_node` fillers.

use std::sync::{Mutex, MutexGuard};

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

/// The encoding is SECRET KEY MATERIAL: it carries the seed.
#[derive(Debug, Serialize, Deserialize)]
pub struct XmssSecretKey {
    pub(crate) epoch_start: Epoch,
    pub(crate) epoch_end: Epoch,
    pub(crate) public_param: PublicParam,
    pub(crate) seed: [u8; 32],
    pub(crate) split_level: usize,
    pub(crate) top: Vec<Vec<Digest>>,
    #[serde(skip)]
    pub(crate) cache: Mutex<Option<BottomSubtree>>,
}

#[derive(Debug)]
pub(crate) struct BottomSubtree {
    subtree_index: u64,
    layers: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub merkle_proof: [Digest; LOG_LIFETIME],
}

/// Ordered lexicographically on `flatten()`, which is what an aggregate's signer
/// set is sorted and deduplicated by.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

impl XmssPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0u8; PUB_KEY_SIZE];
        out[..DIGEST_LEN].copy_from_slice(&self.merkle_root);
        out[DIGEST_LEN..].copy_from_slice(&self.public_param);
        out
    }
}

// PRF domains for secret derivation and filler nodes.
const PRF_DOMAINSEP_WOTS_SECRET_KEY: u32 = 1000;
const PRF_DOMAINSEP_PUBLIC_PARAM: u32 = 1001;
const PRF_DOMAINSEP_RANDOM_NODE: u32 = 1002;

fn prf(seed: &[u8; 32], domain: u32, a: u64, b: u64) -> Digest {
    let mut msg = [0u8; 20];
    msg[..4].copy_from_slice(&domain.to_le_bytes());
    msg[4..12].copy_from_slice(&a.to_le_bytes());
    msg[12..20].copy_from_slice(&b.to_le_bytes());
    primitives::hash::keyed_hash(seed, &msg)[..DIGEST_LEN]
        .try_into()
        .unwrap()
}

fn gen_wots_secret_key(seed: &[u8; 32], epoch: Epoch) -> WotsSecretKey {
    let pre_images = std::array::from_fn(|i| prf(seed, PRF_DOMAINSEP_WOTS_SECRET_KEY, epoch as u64, i as u64));
    WotsSecretKey::new(pre_images)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    prf(seed, PRF_DOMAINSEP_PUBLIC_PARAM, 0, 0)
}

fn gen_random_node(seed: &[u8; 32], level: usize, index: u64) -> Digest {
    prf(seed, PRF_DOMAINSEP_RANDOM_NODE, level as u64, index)
}

/// Merkle parent at `level` (1 compression: both children fill one block).
fn merkle_node(public_param: &PublicParam, level: usize, index: u64, left: &Digest, right: &Digest) -> Digest {
    let mut data = [0u8; 2 * DIGEST_LEN];
    data[..DIGEST_LEN].copy_from_slice(left);
    data[DIGEST_LEN..].copy_from_slice(right);
    tweak_hash(public_param, TWEAK_TYPE_MERKLE, level as u32, index as u32, &data)
}

/// Level-0 layer: WOTS public-key hashes for the in-range leaves `[lo, hi]`.
///
/// Sequential: this runs once per bottom subtree, and the subtrees are what
/// [`key_gen`] fans out over.
fn leaf_layer(seed: &[u8; 32], public_param: &PublicParam, first_epoch: u64, last_epoch: u64) -> Vec<Digest> {
    (first_epoch..=last_epoch)
        .map(|epoch| {
            gen_wots_secret_key(seed, epoch as Epoch)
                .public_key(public_param, epoch as Epoch)
                .hash(public_param, epoch as Epoch)
        })
        .collect()
}

/// Build levels `(from_level+1)..=to_level` onto `layers`; out-of-range children
/// use `gen_random_node`.
///
/// Sequential: each level depends on the one below it, and every level here is at
/// most `O(sqrt(R))` wide, whether it is a bottom subtree's levels or the top part
/// built from the subtree roots.
fn build_up(
    seed: &[u8; 32],
    public_param: &PublicParam,
    layers: &mut Vec<Vec<Digest>>,
    first_epoch: u64,
    last_epoch: u64,
    from_level: usize,
    to_level: usize,
) {
    for level in (from_level + 1)..=to_level {
        let (first_node, last_node) = (first_epoch >> level, last_epoch >> level);
        let (first_child, last_child) = (first_epoch >> (level - 1), last_epoch >> (level - 1));
        let children = layers.last().unwrap();
        let nodes: Vec<Digest> = (first_node..=last_node)
            .map(|index| {
                let child = |child_index: u64| {
                    if child_index >= first_child && child_index <= last_child {
                        children[(child_index - first_child) as usize]
                    } else {
                        gen_random_node(seed, level - 1, child_index)
                    }
                };
                merkle_node(public_param, level, index, &child(2 * index), &child(2 * index + 1))
            })
            .collect();
        layers.push(nodes);
    }
}

fn subtree_bounds(epoch_start: u64, epoch_end: u64, split_level: usize, subtree_index: u64) -> (u64, u64) {
    (
        epoch_start.max(subtree_index << split_level),
        epoch_end.min(((subtree_index + 1) << split_level) - 1),
    )
}

fn build_subtree_layers(
    seed: &[u8; 32],
    public_param: &PublicParam,
    first_epoch: u64,
    last_epoch: u64,
    to_level: usize,
) -> Vec<Vec<Digest>> {
    let mut layers = vec![leaf_layer(seed, public_param, first_epoch, last_epoch)];
    build_up(seed, public_param, &mut layers, first_epoch, last_epoch, 0, to_level);
    layers
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

impl std::fmt::Display for XmssKeyGenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRange => write!(f, "epoch_start is past epoch_end"),
        }
    }
}

impl std::error::Error for XmssKeyGenError {}

/// A fresh key pair, able to sign at each epoch of `epoch_start..=epoch_end`
/// once. The seed comes from `rng`, so nothing can regenerate the key.
pub fn key_gen(
    rng: &mut impl CryptoRng,
    epoch_start: Epoch,
    epoch_end: Epoch,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    key_gen_from_seed(rng.random(), epoch_start, epoch_end)
}

/// Deterministic [`key_gen`]: one `(seed, epoch range)` always regenerates the
/// same key pair, the seed being the key's entire secret material.
pub fn key_gen_from_seed(
    seed: [u8; 32],
    epoch_start: Epoch,
    epoch_end: Epoch,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if epoch_start > epoch_end {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param = gen_public_param(&seed);
    let (first_epoch, last_epoch) = (epoch_start as u64, epoch_end as u64);

    let split_level = primitives::log2_ceil_usize((last_epoch - first_epoch + 1) as usize).div_ceil(2);

    // The bottom subtrees are the only fan-out in key generation: `O(sqrt(R))` of
    // them, each independent, each holding only its own `O(sqrt(R))` layers, so
    // peak memory stays `O(sqrt(R))` and one flat dispatch covers the whole tree.
    // Everything below this is sequential by construction.
    let first_subtree = first_epoch >> split_level;
    let last_subtree = last_epoch >> split_level;
    let root_layer: Vec<Digest> = parallel::map_collect((last_subtree - first_subtree + 1) as usize, |i| {
        let subtree = first_subtree + i as u64;
        let (first_leaf, last_leaf) = subtree_bounds(first_epoch, last_epoch, split_level, subtree);
        build_subtree_layers(&seed, &public_param, first_leaf, last_leaf, split_level)[split_level][0]
    });

    let mut top = vec![root_layer];
    build_up(
        &seed,
        &public_param,
        &mut top,
        first_epoch,
        last_epoch,
        split_level,
        LOG_LIFETIME,
    );

    let pub_key = XmssPublicKey {
        merkle_root: top.last().unwrap()[0],
        public_param,
    };
    let secret_key = XmssSecretKey {
        epoch_start,
        epoch_end,
        public_param,
        seed,
        split_level,
        top,
        cache: Mutex::new(None),
    };
    Ok((secret_key, pub_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignError {
    EpochOutOfRange,
}

impl std::fmt::Display for XmssSignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EpochOutOfRange => write!(f, "the epoch is outside the key's range"),
        }
    }
}

impl std::error::Error for XmssSignError {}

/// WARNING: XMSS is a stateful signature scheme, never sign twice with the same
/// `epoch`. (Even signing the same message twice at the same epoch is insecure,
/// because the signature randomness is drawn fresh.)
pub fn sign(
    rng: &mut impl CryptoRng,
    secret_key: &XmssSecretKey,
    message: &Message,
    epoch: Epoch,
) -> Result<XmssSignature, XmssSignError> {
    if epoch < secret_key.epoch_start || epoch > secret_key.epoch_end {
        return Err(XmssSignError::EpochOutOfRange);
    }
    let (randomness, encoding, _) = find_randomness_for_wots_encoding(message, epoch, &secret_key.public_param, rng);
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, epoch);
    let wots_signature = wots_secret_key.sign(&encoding, randomness, epoch, &secret_key.public_param);

    let cache = secret_key.cached_bottom_subtree(epoch);
    let subtree = cache.as_ref().unwrap();
    let merkle_proof = std::array::from_fn(|level| {
        let neighbour_index = ((epoch as u64) >> level) ^ 1;
        secret_key.merkle_sibling(level, neighbour_index, subtree)
    });
    drop(cache);
    Ok(XmssSignature {
        wots_signature,
        merkle_proof,
    })
}

impl XmssSecretKey {
    /// The epochs this key can sign at. XMSS forbids signing twice at one, so
    /// the caller has to track which of these it has spent.
    pub fn epoch_range(&self) -> std::ops::RangeInclusive<Epoch> {
        self.epoch_start..=self.epoch_end
    }

    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            merkle_root: self.top.last().unwrap()[0],
            public_param: self.public_param,
        }
    }

    /// Warms the signing cache for `epoch`: when the next epoch to sign at is
    /// known in advance, calling this ahead of time makes the [`sign`] faster.
    pub fn prepare(&self, epoch: Epoch) -> Result<(), XmssSignError> {
        if epoch < self.epoch_start || epoch > self.epoch_end {
            return Err(XmssSignError::EpochOutOfRange);
        }
        drop(self.cached_bottom_subtree(epoch));
        Ok(())
    }

    /// The bottom subtree covering `epoch`, rebuilt only on a miss: one subtree
    /// serves all `2^split_level` epochs under it.
    fn cached_bottom_subtree(&self, epoch: Epoch) -> MutexGuard<'_, Option<BottomSubtree>> {
        let subtree_index = (epoch as u64) >> self.split_level;
        let mut cache = self.cache.lock().unwrap();
        if cache.as_ref().is_none_or(|s| s.subtree_index != subtree_index) {
            *cache = Some(self.build_bottom_subtree(subtree_index));
        }
        cache
    }

    fn build_bottom_subtree(&self, subtree_index: u64) -> BottomSubtree {
        let (lo, hi) = subtree_bounds(
            self.epoch_start as u64,
            self.epoch_end as u64,
            self.split_level,
            subtree_index,
        );
        let layers = build_subtree_layers(&self.seed, &self.public_param, lo, hi, self.split_level);
        BottomSubtree { subtree_index, layers }
    }

    /// Authentication-path sibling at `level`: from the top part, the cached
    /// subtree, or `gen_random_node`.
    fn merkle_sibling(&self, level: usize, neighbour_index: u64, subtree: &BottomSubtree) -> Digest {
        let (first_epoch, last_epoch, level_base, layers) = if level >= self.split_level {
            (
                self.epoch_start as u64,
                self.epoch_end as u64,
                self.split_level,
                &self.top,
            )
        } else {
            let (first_epoch, last_epoch) = subtree_bounds(
                self.epoch_start as u64,
                self.epoch_end as u64,
                self.split_level,
                subtree.subtree_index,
            );
            (first_epoch, last_epoch, 0, &subtree.layers)
        };
        let first_node = first_epoch >> level;
        if neighbour_index >= first_node && neighbour_index <= (last_epoch >> level) {
            layers[level - level_base][(neighbour_index - first_node) as usize]
        } else {
            gen_random_node(&self.seed, level, neighbour_index)
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssVerifyError {
    InvalidWots,
    InvalidMerklePath,
}

impl std::fmt::Display for XmssVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidWots => write!(f, "the WOTS signature does not recover a public key"),
            Self::InvalidMerklePath => write!(f, "the authentication path does not reach the key's root"),
        }
    }
}

impl std::error::Error for XmssVerifyError {}

pub fn verify(
    pub_key: &XmssPublicKey,
    message: &Message,
    signature: &XmssSignature,
    epoch: Epoch,
) -> Result<(), XmssVerifyError> {
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(message, epoch, &pub_key.public_param)
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current = wots_public_key.hash(&pub_key.public_param, epoch);
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = ((epoch as u64 >> level) & 1) == 0;
        let parent_index = (epoch as u64) >> (level + 1);
        let (left, right) = if is_left {
            (current, *neighbour)
        } else {
            (*neighbour, current)
        };
        current = merkle_node(&pub_key.public_param, level + 1, parent_index, &left, &right);
    }
    if current == pub_key.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
