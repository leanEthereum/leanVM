//! The hypertree and the three algorithms: `d = 5` layers of height-4 Merkle
//! trees over WOTS+ keys, layer 0 signing the FORS key the message digest
//! picks, the top layer's single root being the public key.
//!
//! The digest `H_msg` names a hypertree leaf `htIdx` and the FORS indices, so a
//! key answers for all `2^h` leaves with nothing reserved or spent: the scheme
//! is stateless.

use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};

use crate::*;

/// `(pkRoot, pkSeed)`. Ordered lexicographically on [`Self::flatten`], which is
/// what an aggregate's signer list is sorted and deduplicated by. The on-chain
/// form is two `bytes32`, each value top-aligned (`v ‖ 0^16`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SphincsPublicKey {
    pub root: Digest,
    pub public_param: PublicParam,
}

impl SphincsPublicKey {
    pub fn flatten(&self) -> [u8; PUB_KEY_SIZE] {
        let mut out = [0; PUB_KEY_SIZE];
        out[..N].copy_from_slice(&self.root);
        out[N..].copy_from_slice(&self.public_param);
        out
    }

    pub fn from_bytes(bytes: &[u8; PUB_KEY_SIZE]) -> Self {
        Self {
            root: bytes[..N].try_into().unwrap(),
            public_param: bytes[N..].try_into().unwrap(),
        }
    }

    /// The verifier's `(pkSeed, pkRoot)` arguments. Always canonical (low 128
    /// bits zero), which the EVM verifier requires.
    pub fn to_bytes32(&self) -> ([u8; 32], [u8; 32]) {
        (word(&self.public_param), word(&self.root))
    }
}

/// A secret key: its 32-byte master secret and nothing else. FIPS 205's three
/// seeds and the public key are derived from it (see [`key_gen_from_seed`]).
#[derive(Clone)]
pub struct SphincsSecretKey {
    master: MasterSecret,
}

impl std::fmt::Debug for SphincsSecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SphincsSecretKey").finish_non_exhaustive()
    }
}

impl SphincsSecretKey {
    /// SECRET KEY MATERIAL: the master secret.
    pub fn to_bytes(&self) -> [u8; SECRET_KEY_SIZE] {
        self.master
    }

    /// Inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8; SECRET_KEY_SIZE]) -> Self {
        Self { master: *bytes }
    }

    /// The public key, derived: the root is the top layer's tree, `2^h'` WOTS
    /// keys, so this costs about a fifth of a signature.
    pub fn public_key(&self) -> SphincsPublicKey {
        let (sk_seed, _, public_param) = derive_seeds(&self.master);
        SphincsPublicKey {
            root: root_of(&public_param, &sk_seed),
            public_param,
        }
    }
}

/// One hypertree layer of a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HtLayer {
    /// `σ`: chain `i` at position `digit_i`.
    pub chains: [Digest; L],
    /// The Merkle authentication path, bottom first.
    pub path: [Digest; SUBTREE_H],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SphincsSignature {
    /// `R`.
    pub randomizer: Randomizer,
    /// One opened leaf secret per FORS tree.
    pub fors_secrets: [Digest; K],
    /// Each tree's authentication path, bottom first.
    pub fors_paths: [[Digest; A]; K],
    /// Layer 0 first.
    pub layers: [HtLayer; D],
}

impl SphincsSignature {
    /// The verifier's blob, exactly [`SIG_SIZE`] bytes: `R ‖ k × [secret ‖ a path
    /// nodes] ‖ d × [l chains ‖ h' path nodes]`.
    pub fn to_bytes(&self) -> [u8; SIG_SIZE] {
        let mut out = [0; SIG_SIZE];
        let mut at = 0;
        let mut put = |bytes: &[u8]| {
            out[at..at + bytes.len()].copy_from_slice(bytes);
            at += bytes.len();
        };
        put(&self.randomizer);
        for (secret, path) in self.fors_secrets.iter().zip(&self.fors_paths) {
            put(secret);
            path.iter().for_each(|s| put(s));
        }
        for layer in &self.layers {
            layer.chains.iter().for_each(|s| put(s));
            layer.path.iter().for_each(|s| put(s));
        }
        debug_assert_eq!(at, SIG_SIZE);
        out
    }

    pub fn from_bytes(bytes: &[u8; SIG_SIZE]) -> Self {
        let at = std::cell::Cell::new(0);
        let take = |len: usize| {
            let s = &bytes[at.get()..at.get() + len];
            at.set(at.get() + len);
            s
        };
        let digest = || -> Digest { take(N).try_into().unwrap() };
        let randomizer = digest();
        let trees: [(Digest, [Digest; A]); K] = std::array::from_fn(|_| (digest(), std::array::from_fn(|_| digest())));
        let fors_secrets = trees.map(|(secret, _)| secret);
        let fors_paths = trees.map(|(_, path)| path);
        let layers = std::array::from_fn(|_| {
            let chains = std::array::from_fn(|_| digest());
            let path = std::array::from_fn(|_| digest());
            HtLayer { chains, path }
        });
        debug_assert_eq!(at.get(), SIG_SIZE);
        Self {
            randomizer,
            fors_secrets,
            fors_paths,
            layers,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SphincsVerifyError {
    /// The hypertree walk does not reach the key's root: the only way a
    /// well-formed signature fails, there being no grinding predicate to check.
    RootMismatch,
}

impl std::fmt::Display for SphincsVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootMismatch => write!(f, "the hypertree walk does not reach the key's root"),
        }
    }
}

impl std::error::Error for SphincsVerifyError {}

/// `(tree, leaf)` on layer `layer` of hypertree leaf `ht_idx`.
pub fn ht_position(ht_idx: u32, layer: usize) -> (u64, u32) {
    let below = ht_idx >> (layer * SUBTREE_H);
    (u64::from(below >> SUBTREE_H), below & ((1 << SUBTREE_H) - 1))
}

/// `Gen` on a fresh key: the master secret comes from `rng`.
pub fn key_gen(rng: &mut impl CryptoRng) -> (SphincsSecretKey, SphincsPublicKey) {
    key_gen_from_seed(rng.random())
}

/// `SK.seed`, `SK.prf` and `PK.seed` from a master secret: each
/// `keccak256(tag ‖ master)[..16]`, `tag` one of `"SPHINCS-v2 SK.seed"`,
/// `"SPHINCS-v2 SK.prf"`, `"SPHINCS-v2 PK.seed"`: three hash domains, so the
/// seeds are independent. (Signer-private: no verifier sees the derivation.)
fn derive_seeds(master: &MasterSecret) -> ([u8; N], [u8; N], PublicParam) {
    let seed = |tag: &[u8]| truncate(&primitives::keccak::keccak256(&[tag, master].concat()));
    (
        seed(b"SPHINCS-v2 SK.seed"),
        seed(b"SPHINCS-v2 SK.prf"),
        seed(b"SPHINCS-v2 PK.seed"),
    )
}

/// Deterministic `Gen` on the master secret `master`. The three seeds are each
/// `keccak256(tag ‖ master)[..16]`, `tag` one of `"SPHINCS-v2 SK.seed"`,
/// `"SPHINCS-v2 SK.prf"`, `"SPHINCS-v2 PK.seed"`.
pub fn key_gen_from_seed(master: MasterSecret) -> (SphincsSecretKey, SphincsPublicKey) {
    let sk = SphincsSecretKey { master };
    let pk = sk.public_key();
    (sk, pk)
}

/// The public root: the top layer's single tree.
fn root_of(public_param: &PublicParam, sk_seed: &[u8; N]) -> Digest {
    subtree_levels(public_param, sk_seed, (D - 1) as u32, 0)[SUBTREE_H][0]
}

/// Sign. Deterministic and stateless.
///
/// The key's root is rebuilt first ([`SphincsSecretKey::public_key`]), since
/// the message digest depends on it.
pub fn sign(sk: &SphincsSecretKey, message: &Message) -> SphincsSignature {
    let (sk_seed, sk_prf, public_param) = derive_seeds(&sk.master);
    sign_with_seeds(sk_seed, sk_prf, public_param, message).1
}

/// Key generation and signing on the three seeds given directly, as FIPS 205
/// and NiceTry's reference signer (`scripts/sphincs_v2_reference.py`) state them.
/// For reproducing reference vectors: a key made this way has no master secret,
/// so use [`key_gen`] / [`key_gen_from_seed`] for real keys.
pub fn sign_with_seeds(
    sk_seed: [u8; N],
    sk_prf: [u8; N],
    public_param: PublicParam,
    message: &Message,
) -> (SphincsPublicKey, SphincsSignature) {
    let root = root_of(&public_param, &sk_seed);
    let signature = sign_with(&public_param, &root, &sk_seed, &sk_prf, message);
    (SphincsPublicKey { root, public_param }, signature)
}

fn sign_with(
    pp: &PublicParam,
    root: &Digest,
    sk_seed: &[u8; N],
    sk_prf: &[u8; N],
    message: &Message,
) -> SphincsSignature {
    let randomizer = randomizer(sk_prf, message);
    let d = h_msg(pp, root, &randomizer, message);
    let ht_idx = ht_index(&d);
    let (fors_secrets, fors_paths, fors_pk) = fors_sign(pp, sk_seed, ht_idx, &fors_indices(&d));

    let mut node = fors_pk;
    let layers = std::array::from_fn(|layer| {
        let (tree, leaf) = ht_position(ht_idx, layer);
        let chains = wots_sign(pp, sk_seed, layer as u32, tree, leaf, &node);
        let levels = subtree_levels(pp, sk_seed, layer as u32, tree);
        node = levels[SUBTREE_H][0];
        HtLayer {
            chains,
            path: auth_path(&levels, leaf),
        }
    });
    debug_assert_eq!(&node, root);

    SphincsSignature {
        randomizer,
        fors_secrets,
        fors_paths,
        layers,
    }
}

/// Everything a verification computes on the way to the root, for provers that
/// replay it: the digest, what it selects, and what each layer signs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyTrace {
    pub digest: [u8; 32],
    pub ht_idx: u32,
    pub fors_indices: [u32; K],
    /// `signed[layer]`: the node layer `layer`'s WOTS key signs (the FORS key on
    /// layer 0); `signed[d]` is the root reached.
    pub signed: [Digest; D + 1],
    /// Each layer's WOTS digits, the checksum's last.
    pub digits: [[u8; L]; D],
}

/// Replay a verification up to the root comparison.
pub fn verify_trace(pk: &SphincsPublicKey, message: &Message, signature: &SphincsSignature) -> VerifyTrace {
    let pp = &pk.public_param;
    let digest = h_msg(pp, &pk.root, &signature.randomizer, message);
    let indices = fors_indices(&digest);
    let ht_idx = ht_index(&digest);
    let mut signed = [[0; N]; D + 1];
    let mut digits_of = [[0; L]; D];
    signed[0] = fors_pk_from_sig(pp, ht_idx, &indices, &signature.fors_secrets, &signature.fors_paths);
    for (layer, sig) in signature.layers.iter().enumerate() {
        let (tree, leaf) = ht_position(ht_idx, layer);
        digits_of[layer] = digits(&signed[layer]);
        let wots_pk = wots_pk_from_sig(pp, layer as u32, tree, leaf, &signed[layer], &sig.chains);
        signed[layer + 1] = tree_fold(pp, layer as u32, tree, leaf, wots_pk, &sig.path);
    }
    VerifyTrace {
        digest,
        ht_idx,
        fors_indices: indices,
        signed,
        digits: digits_of,
    }
}

/// `Ver`, `SphincsVerifier_v2.verify` on the signature's blob.
pub fn verify(
    pk: &SphincsPublicKey,
    message: &Message,
    signature: &SphincsSignature,
) -> Result<(), SphincsVerifyError> {
    if verify_trace(pk, message, signature).signed[D] == pk.root {
        Ok(())
    } else {
        Err(SphincsVerifyError::RootMismatch)
    }
}
