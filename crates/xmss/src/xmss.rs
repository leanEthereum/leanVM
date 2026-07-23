use std::sync::Mutex;

use backend::*;
use rand::{CryptoRng, RngExt, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

use crate::wots::*;
use crate::*;

/// Memory-optimized secret key for a range of R = slot_end - slot_start + 1 slots: O(sqrt(R) +
/// LOG_LIFETIME) instead of O(R). Stores the top tree (in-range band plus a thin spine) and one
/// cached bottom subtree, cut at split_level = log2(R)/2. Out-of-range nodes are deterministic
/// gen_random_node fillers; see `xmss_small_memory.tex` for the picture.
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

impl std::fmt::Debug for XmssSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("XmssSecretKey")
            .field("slot_start", &self.slot_start)
            .field("slot_end", &self.slot_end)
            .field("split_level", &self.split_level)
            .finish_non_exhaustive()
    }
}

/// Bottom subtree covering the last-signed slot; its leaf range is derived from `subtree_index`.
#[derive(Debug)]
pub(crate) struct BottomSubtree {
    subtree_index: u64, // = slot >> split_level
    layers: Vec<Vec<Digest>>,
}

/// Format version of the persisted secret key; bump on layout changes.
const SECRET_KEY_FORMAT_VERSION: u8 = 1;

/// Persists (version, seed, slot range, top tree). The top tree is stored so that loading a
/// key is cheap (no re-hashing of the whole range); the derived fields (public_param,
/// split_level) are recomputed and the tree shape revalidated. The bottom-subtree cache
/// restarts empty.
impl Serialize for XmssSecretKey {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (
            SECRET_KEY_FORMAT_VERSION,
            &self.seed,
            self.slot_start,
            self.slot_end,
            &self.top,
        )
            .serialize(s)
    }
}

impl<'de> Deserialize<'de> for XmssSecretKey {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (version, seed, slot_start, slot_end, top) = <(u8, [u8; 32], u32, u32, Vec<Vec<Digest>>)>::deserialize(d)?;
        if version != SECRET_KEY_FORMAT_VERSION {
            return Err(serde::de::Error::custom(format!(
                "unsupported secret key format version {version} (expected {SECRET_KEY_FORMAT_VERSION})"
            )));
        }
        Self::from_parts(seed, slot_start, slot_end, top).map_err(serde::de::Error::custom)
    }
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
    pub fn flatten(&self) -> [F; PUB_KEY_FLAT_SIZE] {
        let mut output = [F::default(); PUB_KEY_FLAT_SIZE];
        output[..XMSS_DIGEST_LEN].copy_from_slice(&self.merkle_root);
        output[XMSS_DIGEST_LEN..].copy_from_slice(&self.public_param);
        output
    }
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u32, public_param: PublicParam) -> WotsSecretKey {
    let rng_seed_fe = poseidon_prf(PRF_DOMAINSEP_WOTS_SECRET_KEY, seed, [slot as usize, 0]);
    let mut rng_seed = [0u8; 32];
    for (chunk, f) in rng_seed.as_chunks_mut::<4>().0.iter_mut().zip(rng_seed_fe) {
        *chunk = f.as_canonical_u32().to_le_bytes();
    }
    let mut rng = StdRng::from_seed(rng_seed);
    WotsSecretKey::random(&mut rng, public_param, slot)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    poseidon_prf(PRF_DOMAINSEP_PUBLIC_PARAM, seed, [0, 0])[..PUBLIC_PARAM_LEN_FE]
        .try_into()
        .unwrap()
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 32], level: usize, index: usize) -> Digest {
    poseidon_prf(PRF_DOMAINSEP_RANDOM_NODE, seed, [level, index])[..XMSS_DIGEST_LEN]
        .try_into()
        .unwrap()
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

impl std::fmt::Display for XmssKeyGenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidRange => write!(
                f,
                "invalid slot range (empty, reversed, or beyond the 2^{LOG_LIFETIME} lifetime)"
            ),
        }
    }
}

impl std::error::Error for XmssKeyGenError {}

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
                    gen_random_node(seed, level - 1, left_idx as usize)
                };
                let right = if right_idx >= prev_base && right_idx <= prev_top {
                    prev[(right_idx - prev_base) as usize]
                } else {
                    gen_random_node(seed, level - 1, right_idx as usize)
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

/// Generates a new key pair, active for the `num_active_slots` slots starting at
/// `activation_slot` (both ends must stay within the `2^LOG_LIFETIME` lifetime).
pub fn xmss_key_gen<R: CryptoRng>(
    rng: &mut R,
    activation_slot: u64,
    num_active_slots: u64,
) -> Result<(XmssPublicKey, XmssSecretKey), XmssKeyGenError> {
    xmss_key_gen_from_seed(rng.random(), activation_slot, num_active_slots)
}

/// Deterministic [`xmss_key_gen`]: the same (seed, activation range) always regenerates the
/// same key pair. The seed is the key's entire secret material.
pub fn xmss_key_gen_from_seed(
    seed: [u8; 32],
    activation_slot: u64,
    num_active_slots: u64,
) -> Result<(XmssPublicKey, XmssSecretKey), XmssKeyGenError> {
    let activation_end = activation_slot
        .checked_add(num_active_slots)
        .ok_or(XmssKeyGenError::InvalidRange)?;
    if num_active_slots == 0 || activation_end > 1 << LOG_LIFETIME {
        return Err(XmssKeyGenError::InvalidRange);
    }

    // The pool forbids nested dispatch: build sequentially when key gen itself already runs
    // inside a pool task (e.g. generating many keys in a parallel batch).
    let sequential = parallel::is_in_pool_task();

    let public_param: PublicParam = gen_public_param(&seed);
    let lo = activation_slot;
    let hi = activation_end - 1;

    // ~sqrt(R) leaves per bottom subtree; always <= LOG_LIFETIME/2 since R <= 2^LOG_LIFETIME.
    let split_level = log2_ceil_usize(num_active_slots as usize).div_ceil(2);

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
        slot_start: activation_slot as u32,
        slot_end: hi as u32,
        public_param,
        seed,
        split_level,
        top,
        cache: Mutex::new(None),
    };
    Ok((pub_key, secret_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignatureError {
    SlotOutOfRange,
    EncodingAttemptsExceeded,
}

impl std::fmt::Display for XmssSignatureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SlotOutOfRange => write!(f, "slot is outside the key's valid range"),
            Self::EncodingAttemptsExceeded => {
                write!(f, "no valid WOTS encoding found within {MAX_SIGNING_ATTEMPTS} attempts")
            }
        }
    }
}

impl std::error::Error for XmssSignatureError {}

/// Deterministic encoding randomness: a seed-keyed Poseidon PRF over (slot, attempt), mixed
/// with the hashed message by one more compression.
fn derive_signature_randomness(
    seed: &[u8; 32],
    slot: u32,
    message_fe: &[F; MESSAGE_LEN_FE],
    attempt: usize,
) -> Randomness {
    let prf = poseidon_prf(PRF_DOMAINSEP_SIGNATURE_RANDOMNESS, seed, [slot as usize, attempt]);
    let mut input = [F::ZERO; POSEIDON1_WIDTH];
    input[..DIGEST_LEN_FE].copy_from_slice(&prf);
    input[DIGEST_LEN_FE..].copy_from_slice(message_fe);
    poseidon16_compress(input)[..RANDOMNESS_LEN_FE].try_into().unwrap()
}

/// WARNING: XMSS is a stateful signature scheme, never sign two different messages at the same
/// `slot`. Signing is derandomized (the encoding randomness is derived from the secret key,
/// slot, and message), so calling this twice with the same (slot, message) pair returns the
/// same signature and is harmless.
pub fn xmss_sign(
    secret_key: &XmssSecretKey,
    slot: u32,
    message: &[u8; MESSAGE_LEN_BYTES],
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.slot_start || slot > secret_key.slot_end {
        return Err(XmssSignatureError::SlotOutOfRange);
    }
    let message_fe = hash_message(message);
    let pub_key = secret_key.public_key();
    let (randomness, encoding) = (0..MAX_SIGNING_ATTEMPTS)
        .find_map(|attempt| {
            let randomness = derive_signature_randomness(&secret_key.seed, slot, &message_fe, attempt);
            wots_encode(&message_fe, slot, &pub_key, &randomness).map(|encoding| (randomness, encoding))
        })
        .ok_or(XmssSignatureError::EncodingAttemptsExceeded)?;
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot, secret_key.public_param);
    let wots_signature = wots_secret_key.sign_with_encoding(randomness, &encoding, secret_key.public_param, slot);
    let cache = secret_key.cached_bottom_subtree(slot);
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

    /// The slots this key can sign for.
    pub const fn activation_slots(&self) -> std::ops::RangeInclusive<u32> {
        self.slot_start..=self.slot_end
    }

    /// Warms the signing cache for `slot`: when the next signing slot is known in advance,
    /// calling this ahead of time makes the subsequent `xmss_sign` faster.
    pub fn prepare(&self, slot: u32) -> Result<(), XmssSignatureError> {
        if slot < self.slot_start || slot > self.slot_end {
            return Err(XmssSignatureError::SlotOutOfRange);
        }
        drop(self.cached_bottom_subtree(slot));
        Ok(())
    }

    /// Rebuild a secret key from its persisted parts, recomputing the derived fields and
    /// revalidating the top tree's shape (its content is trusted, exactly like the seed).
    pub(crate) fn from_parts(
        seed: [u8; 32],
        slot_start: u32,
        slot_end: u32,
        top: Vec<Vec<Digest>>,
    ) -> Result<Self, &'static str> {
        if slot_start > slot_end {
            return Err("invalid slot range");
        }
        let (lo, hi) = (slot_start as u64, slot_end as u64);
        let split_level = log2_ceil_usize((hi - lo + 1) as usize).div_ceil(2);
        let expected_layer_lens =
            (split_level..=LOG_LIFETIME).map(|level| ((hi >> level) - (lo >> level) + 1) as usize);
        if top.len() != LOG_LIFETIME - split_level + 1
            || top
                .iter()
                .zip(expected_layer_lens)
                .any(|(layer, len)| layer.len() != len)
        {
            return Err("top tree shape does not match the slot range");
        }
        Ok(Self {
            slot_start,
            slot_end,
            public_param: gen_public_param(&seed),
            seed,
            split_level,
            top,
            cache: Mutex::new(None),
        })
    }

    fn cached_bottom_subtree(&self, slot: u32) -> std::sync::MutexGuard<'_, Option<BottomSubtree>> {
        let subtree_index = (slot as u64) >> self.split_level;
        let mut cache = self.cache.lock().unwrap();
        if cache.as_ref().is_none_or(|s| s.subtree_index != subtree_index) {
            *cache = Some(self.build_bottom_subtree(subtree_index));
        }
        cache
    }

    /// (Re)build the bottom subtree with the given index. Always sequential: signing must
    /// never wait on the thread pool while it holds the signing-cache mutex (a pool task
    /// blocked on the same key would deadlock the pool, and hence the signer).
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
            gen_random_node(&self.seed, level, neighbour_index as usize)
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
            Self::InvalidWots => write!(f, "invalid WOTS signature (encoding rejected or wrong chain tips)"),
            Self::InvalidMerklePath => write!(f, "merkle path does not lead to the public key's root"),
        }
    }
}

impl std::error::Error for XmssVerifyError {}

pub fn xmss_verify(
    pub_key: &XmssPublicKey,
    slot: u32,
    message: &[u8; MESSAGE_LEN_BYTES],
    signature: &XmssSignature,
) -> Result<(), XmssVerifyError> {
    let message_fe = hash_message(message);
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(&message_fe, slot, pub_key)
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
