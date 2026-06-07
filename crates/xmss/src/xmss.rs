use std::sync::Mutex;

use backend::*;
use rand::{CryptoRng, RngExt, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use sha3::{Digest as Sha3Digest, Keccak256};

use crate::*;

/// Memory-optimized secret key for a range of R = slot_end - slot_start + 1 slots: O(sqrt(R) +
/// LOG_LIFETIME) instead of O(R). Stores the top tree (in-range band plus a thin spine) and one
/// cached bottom subtree, cut at split_level = log2(R)/2. Out-of-range nodes are deterministic
/// gen_random_node fillers; see `xmss_small_memory.tex` for the picture.
#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) slot_start: u32, // inclusive
    pub(crate) slot_end: u32,   // inclusive
    pub(crate) public_param: PublicParam,
    pub(crate) seed: [u8; 32],
    pub(crate) split_level: usize, // bottom-subtree height (2^split_level leaves each)
    // top[l - split_level] = level-l nodes for indices [slot_start >> l, slot_end >> l]
    pub(crate) top: Vec<Vec<Digest>>,
    pub(crate) cache: Mutex<Option<BottomSubtree>>,
}

/// Bottom subtree covering the last-signed slot; its leaf range is derived from `subtree_index`.
#[derive(Debug)]
pub(crate) struct BottomSubtree {
    subtree_index: u64, // = slot >> split_level
    layers: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    #[serde(
        with = "backend::array_serialization",
        bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>")
    )]
    pub merkle_proof: [Digest; LOG_LIFETIME],
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

impl XmssPublicKey {
    pub fn flaten(&self) -> [F; PUB_KEY_FLAT_SIZE] {
        let mut output = [F::default(); PUB_KEY_FLAT_SIZE];
        output[..XMSS_DIGEST_LEN].copy_from_slice(&self.merkle_root);
        output[XMSS_DIGEST_LEN..].copy_from_slice(&self.public_param);
        output
    }
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u32, public_param: PublicParam) -> WotsSecretKey {
    let mut hasher = Keccak256::new();
    hasher.update(b"wots_secret_key");
    hasher.update(seed);
    hasher.update(slot.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    WotsSecretKey::random(&mut rng, public_param, slot)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    let mut hasher = Keccak256::new();
    hasher.update(b"public_param");
    hasher.update(seed);
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    rng.random()
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 32], level: usize, index: u64) -> Digest {
    let mut hasher = Keccak256::new();
    hasher.update(b"random_node");
    hasher.update(seed);
    hasher.update((level as u64).to_le_bytes());
    hasher.update(index.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    rng.random()
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

fn fill<T: Send>(sequential: bool, data: &mut [T], f: impl Fn(usize, &mut T) + Sync) {
    if sequential {
        data.iter_mut().enumerate().for_each(|(i, out)| f(i, out));
    } else {
        parallel::par_for_each_mut(data, f);
    }
}

/// Level-0 layer: WOTS public-key hashes for the in-range leaves `[lo, hi]`.
fn leaf_layer(seed: &[u8; 32], public_param: &PublicParam, lo: u64, hi: u64, sequential: bool) -> Vec<Digest> {
    let mut leaves: Vec<Digest> = unsafe { uninitialized_vec((hi - lo + 1) as usize) };
    fill(sequential, &mut leaves, |k, out| {
        let slot = (lo + k as u64) as u32;
        let wots = gen_wots_secret_key(seed, slot, *public_param);
        *out = wots.public_key().hash(*public_param, slot);
    });
    leaves
}

/// Build levels `(from_level+1)..=to_level` onto `layers`; out-of-range children use `gen_random_node`.
#[allow(clippy::too_many_arguments)]
fn build_up(
    seed: &[u8; 32],
    public_param: &PublicParam,
    layers: &mut Vec<Vec<Digest>>,
    lo: u64,
    hi: u64,
    from_level: usize,
    to_level: usize,
    sequential: bool,
) {
    for level in (from_level + 1)..=to_level {
        let base = lo >> level;
        let top = hi >> level;
        let prev_base = lo >> (level - 1);
        let prev_top = hi >> (level - 1);
        let nodes: Vec<Digest> = {
            let prev = layers.last().unwrap();
            let mut nodes: Vec<Digest> = unsafe { uninitialized_vec((top - base + 1) as usize) };
            fill(sequential, &mut nodes, |k, out| {
                let i = base + k as u64;
                let left_idx = 2 * i;
                let right_idx = 2 * i + 1;
                let left = if left_idx >= prev_base && left_idx <= prev_top {
                    prev[(left_idx - prev_base) as usize]
                } else {
                    gen_random_node(seed, level - 1, left_idx)
                };
                let right = if right_idx >= prev_base && right_idx <= prev_top {
                    prev[(right_idx - prev_base) as usize]
                } else {
                    gen_random_node(seed, level - 1, right_idx)
                };
                let merkle_data = build_merkle_data(
                    make_tweak(TWEAK_TYPE_MERKLE, level, i as u32),
                    public_param,
                    &left,
                    &right,
                );
                *out = poseidon16_compress(merkle_data)[..XMSS_DIGEST_LEN].try_into().unwrap();
            });
            nodes
        };
        layers.push(nodes);
    }
}

/// In-range leaf bounds of the bottom subtree with the given index.
fn subtree_bounds(slot_start: u64, slot_end: u64, split_level: usize, subtree_index: u64) -> (u64, u64) {
    (
        slot_start.max(subtree_index << split_level),
        slot_end.min(((subtree_index + 1) << split_level) - 1),
    )
}

/// Build merkle layers `0..=to_level` for the in-range leaves `[lo, hi]`.
fn build_subtree_layers(
    seed: &[u8; 32],
    public_param: &PublicParam,
    lo: u64,
    hi: u64,
    to_level: usize,
    sequential: bool,
) -> Vec<Vec<Digest>> {
    let mut layers = vec![leaf_layer(seed, public_param, lo, hi, sequential)];
    build_up(seed, public_param, &mut layers, lo, hi, 0, to_level, sequential);
    layers
}

pub fn xmss_key_gen(
    seed: [u8; 32],
    slot_start: u32,
    slot_end: u32,
    sequential: bool,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if slot_start > slot_end || slot_end as u64 >= (1 << LOG_LIFETIME) {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param: PublicParam = gen_public_param(&seed);
    let lo = slot_start as u64;
    let hi = slot_end as u64;

    // ~sqrt(R) leaves per bottom subtree; always <= LOG_LIFETIME/2 since R <= 2^LOG_LIFETIME.
    let split_level = log2_ceil_usize((hi - lo + 1) as usize).div_ceil(2);

    // Roots of each bottom subtree, built one at a time so peak memory stays O(sqrt(R)).
    let first_subtree = lo >> split_level;
    let last_subtree = hi >> split_level;
    let mut root_layer: Vec<Digest> = unsafe { uninitialized_vec((last_subtree - first_subtree + 1) as usize) };
    fill(sequential, &mut root_layer, |k, out| {
        let (in_lo, in_hi) = subtree_bounds(lo, hi, split_level, first_subtree + k as u64);
        *out = build_subtree_layers(&seed, &public_param, in_lo, in_hi, split_level, true)[split_level][0];
    });

    // Top part: levels split_level..=LOG_LIFETIME.
    let mut top = vec![root_layer];
    build_up(
        &seed,
        &public_param,
        &mut top,
        lo,
        hi,
        split_level,
        LOG_LIFETIME,
        sequential,
    );

    let pub_key = XmssPublicKey {
        merkle_root: top.last().unwrap()[0],
        public_param,
    };
    let secret_key = XmssSecretKey {
        slot_start,
        slot_end,
        public_param,
        seed,
        split_level,
        top,
        cache: Mutex::new(None),
    };
    Ok((secret_key, pub_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignatureError {
    SlotOutOfRange,
    InvalidRandomness,
}

pub fn xmss_sign<R: CryptoRng>(
    rng: &mut R,
    secret_key: &XmssSecretKey,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<XmssSignature, XmssSignatureError> {
    let (randomness, _, _) = find_randomness_for_wots_encoding(message, slot, &secret_key.public_key(), rng);
    xmss_sign_with_randomness(secret_key, message, slot, randomness)
}

pub fn xmss_sign_with_randomness(
    secret_key: &XmssSecretKey,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    randomness: [F; RANDOMNESS_LEN_FE],
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.slot_start || slot > secret_key.slot_end {
        return Err(XmssSignatureError::SlotOutOfRange);
    }
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot, secret_key.public_param);
    let wots_signature = wots_secret_key
        .sign_with_randomness(message, slot, &secret_key.public_key(), randomness)
        .ok_or(XmssSignatureError::InvalidRandomness)?;
    // Cache the bottom subtree covering `slot` (reused across its 2^split_level slots), then read the path.
    let subtree_index = (slot as u64) >> secret_key.split_level;
    let mut cache = secret_key.cache.lock().unwrap();
    if cache.as_ref().is_none_or(|s| s.subtree_index != subtree_index) {
        *cache = Some(secret_key.build_bottom_subtree(subtree_index));
    }
    let sub = cache.as_ref().unwrap();
    let merkle_proof = std::array::from_fn(|level| {
        let neighbour_index = ((slot as u64) >> level) ^ 1;
        secret_key.merkle_sibling(level, neighbour_index, sub)
    });
    drop(cache);
    Ok(XmssSignature {
        wots_signature,
        merkle_proof,
    })
}

impl XmssSecretKey {
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            merkle_root: self.top.last().unwrap()[0],
            public_param: self.public_param,
        }
    }

    /// (Re)build the bottom subtree with the given index.
    fn build_bottom_subtree(&self, subtree_index: u64) -> BottomSubtree {
        let (lo, hi) = subtree_bounds(
            self.slot_start as u64,
            self.slot_end as u64,
            self.split_level,
            subtree_index,
        );
        let layers = build_subtree_layers(&self.seed, &self.public_param, lo, hi, self.split_level, true);
        BottomSubtree { subtree_index, layers }
    }

    /// Authentication-path sibling at `level`: from the top part, the cached subtree, or `gen_random_node`.
    fn merkle_sibling(&self, level: usize, neighbour_index: u64, sub: &BottomSubtree) -> Digest {
        let (lo, hi, level_base, layers) = if level >= self.split_level {
            (
                self.slot_start as u64,
                self.slot_end as u64,
                self.split_level,
                &self.top,
            )
        } else {
            let (lo, hi) = subtree_bounds(
                self.slot_start as u64,
                self.slot_end as u64,
                self.split_level,
                sub.subtree_index,
            );
            (lo, hi, 0, &sub.layers)
        };
        let base = lo >> level;
        if neighbour_index >= base && neighbour_index <= (hi >> level) {
            layers[level - level_base][(neighbour_index - base) as usize]
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

pub fn xmss_verify(
    pub_key: &XmssPublicKey,
    message: &[F; MESSAGE_LEN_FE],
    signature: &XmssSignature,
    slot: u32,
) -> Result<(), XmssVerifyError> {
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(message, slot, pub_key)
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current_hash = wots_public_key.hash(pub_key.public_param, slot);
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = (((slot as u64) >> level) & 1) == 0;
        let parent_index = ((slot as u64) >> (level + 1)) as u32;
        let (left_child, right_child) = if is_left {
            (current_hash, *neighbour)
        } else {
            (*neighbour, current_hash)
        };
        let merkle_data = build_merkle_data(
            make_tweak(TWEAK_TYPE_MERKLE, level + 1, parent_index),
            &pub_key.public_param,
            &left_child,
            &right_child,
        );
        current_hash = poseidon16_compress(merkle_data)[..XMSS_DIGEST_LEN].try_into().unwrap();
    }
    if current_hash == pub_key.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
