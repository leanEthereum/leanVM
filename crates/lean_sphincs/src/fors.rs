//! The few-time signature: FORS (FIPS 205 §8).
//!
//! The instance of bottom leaf `idx` has `FORS_TREES` trees of height
//! `FORS_HEIGHT`, whose leaves hash secrets derived from `SK.seed`. The message
//! digest picks a leaf in every tree, and the signature reveals its secret and
//! its path. The FORS public key is `T_k` over the trees' roots, which the bottom
//! one-time key signs.

use crate::*;

/// One FORS tree's opening: the picked leaf's secret, and its path from the
/// leaf up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub(crate) secret: Digest,
    pub(crate) path: [Digest; FORS_HEIGHT],
}

impl ForsTreeOpening {
    pub fn secret(&self) -> &Digest {
        &self.secret
    }
}

pub(crate) type ForsOpening = [ForsTreeOpening; FORS_TREES];

/// Instance `idx`'s address of type `t`: the bottom key's tree, and its leaf as
/// the key pair.
fn fors_adrs(idx: u64, t: u32) -> Adrs {
    OtsKey::of_index(0, idx).adrs(t)
}

/// Node `j` at height `z` of tree `c`: its tree index counts across the trees.
fn fors_node_adrs(idx: u64, c: usize, z: usize, j: usize) -> Adrs {
    fors_adrs(idx, FORS_TREE)
        .with_tree_height(z as u32)
        .with_tree_index(((c << (FORS_HEIGHT - z)) + j) as u32)
}

/// Leaf `s` of tree `c`: `F` of its secret.
fn fors_leaf(pk_seed: &PkSeed, idx: u64, c: usize, s: usize, secret: &Digest) -> Digest {
    th(pk_seed, &fors_node_adrs(idx, c, 0, s), secret)
}

/// Node `j` at height `z` of tree `c`, from its two children.
fn fors_node(pk_seed: &PkSeed, idx: u64, c: usize, z: usize, j: usize, children: &[Digest; 2]) -> Digest {
    th_digests(pk_seed, &fors_node_adrs(idx, c, z, j), children)
}

/// `T_k` over the roots: the FORS public key.
fn fors_key(pk_seed: &PkSeed, idx: u64, roots: &[Digest; FORS_TREES]) -> Digest {
    th_digests(pk_seed, &fors_adrs(idx, FORS_ROOTS), roots)
}

/// `fors_sign` and the public key it opens, each tree being built once: the key
/// of instance `idx`, and its opening at `leaves`.
pub(crate) fn fors_open(sk: &ExpandedKey, idx: u64, leaves: &[usize; FORS_TREES]) -> (Digest, ForsOpening) {
    const LEAVES: usize = 1 << FORS_HEIGHT;
    const SECRET_IN: usize = PREFIX_LEN + SECRET_KEY_LEN;
    const LEAF_IN: usize = PREFIX_LEN + N;
    let pk_seed = &sk.pk_seed;
    let prf_base = fors_adrs(idx, FORS_PRF);
    let tree_base = fors_adrs(idx, FORS_TREE);
    let mut secret_in = vec![0u8; LEAVES * SECRET_IN];
    let mut leaf_in = vec![0u8; LEAVES * LEAF_IN];
    let mut digests = vec![0u8; LEAVES * keccak256::OUT_LEN];
    let mut roots = [[0u8; N]; FORS_TREES];
    let mut openings = Vec::with_capacity(FORS_TREES);
    for (c, root) in roots.iter_mut().enumerate() {
        for (s, input) in secret_in.as_chunks_mut::<SECRET_IN>().0.iter_mut().enumerate() {
            input[..N].copy_from_slice(pk_seed);
            input[N..PREFIX_LEN].copy_from_slice(prf_base.with_tree_index(((c << FORS_HEIGHT) + s) as u32).as_bytes());
            input[PREFIX_LEN..].copy_from_slice(&sk.sk_seed);
        }
        keccak256::hash_many(&secret_in, SECRET_IN, &mut digests);
        let secrets: Vec<Digest> = digests
            .as_chunks::<{ keccak256::OUT_LEN }>()
            .0
            .iter()
            .map(|&d| keccak256::truncate(d))
            .collect();

        for (s, (secret, input)) in secrets.iter().zip(leaf_in.as_chunks_mut::<LEAF_IN>().0).enumerate() {
            input[..N].copy_from_slice(pk_seed);
            input[N..PREFIX_LEN].copy_from_slice(
                tree_base
                    .with_tree_height(0)
                    .with_tree_index(((c << FORS_HEIGHT) + s) as u32)
                    .as_bytes(),
            );
            input[PREFIX_LEN..].copy_from_slice(secret);
        }
        keccak256::hash_many(&leaf_in, LEAF_IN, &mut digests);
        let leaf_hashes: Vec<Digest> = digests
            .as_chunks::<{ keccak256::OUT_LEN }>()
            .0
            .iter()
            .map(|&d| keccak256::truncate(d))
            .collect();

        let levels = merkle_levels_batched(pk_seed, leaf_hashes, FORS_HEIGHT, |z, j| fors_node_adrs(idx, c, z, j));
        let s = leaves[c];
        openings.push(ForsTreeOpening {
            secret: secrets[s],
            path: std::array::from_fn(|z| levels[z][(s >> z) ^ 1]),
        });
        *root = levels[FORS_HEIGHT][0];
    }
    (fors_key(pk_seed, idx, &roots), openings.try_into().unwrap())
}

/// `fors_pkFromSig`: the FORS public key an opening reaches at `leaves`, showing
/// `visit` the two children of every node on the way up.
pub fn fors_recover(
    pk_seed: &PkSeed,
    idx: u64,
    leaves: &[usize; FORS_TREES],
    opening: &ForsOpening,
    mut visit: impl FnMut(&[Digest; 2]),
) -> Digest {
    let roots = std::array::from_fn(|c| {
        let (s, tree) = (leaves[c], &opening[c]);
        let leaf = fors_leaf(pk_seed, idx, c, s, &tree.secret);
        keccak256::path_fold(leaf, s, &tree.path, &mut visit, |z, j, pair| {
            fors_node(pk_seed, idx, c, z, j, pair)
        })
    });
    fors_key(pk_seed, idx, &roots)
}
