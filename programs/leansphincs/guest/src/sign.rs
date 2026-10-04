//! `Gen` and `Sign`.
//!
//! A secret key keeps the top tree's nodes halfway up, a cache and not state.
//!
//! A signature then rebuilds a `2^6`-leaf subtree of it, not all `2^12` leaves.

use crate::*;

/// `A_max`: message digests a signer tries.
const MAX_DIGEST_ATTEMPTS: u64 = 1 << 32;
/// `C_max`: encoding counters a signer tries per layer.
const MAX_ENCODING_ATTEMPTS: u64 = 1 << 32;
/// The level of the top tree the key caches: 6, halfway up.
///
/// A signature then rebuilds `2^6` leaves below it and folds `2^6` nodes above it.
const SPLIT_LEVEL: usize = HEIGHTS[0].div_ceil(2);
/// Nodes the key caches: the whole level, 64.
const CACHE_LEN: usize = 1 << (HEIGHTS[0] - SPLIT_LEVEL);

/// A secret key: `P`, the root, the master secret everything is derived from, and the cache.
#[derive(Clone, Debug)]
pub struct SecretKey {
    /// `P`.
    public_param: PublicParam,
    /// The top tree's root, the public key's.
    root: Digest,
    /// The master secret: the seed.
    master: [u64; 4],
    /// The top tree's nodes at the split level.
    cache: [Digest; CACHE_LEN],
}

/// Why signing failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SphincsSignError {
    /// `A_max` digests in a row had a nonzero last index.
    #[error("A_max digests in a row have a nonzero last index")]
    NoAdmissibleDigest,
    /// `C_max` counters in a row gave no codeword.
    #[error("C_max counters in a row give no codeword")]
    NoAdmissibleEncoding,
}

/// `Gen` from a secret seed: the seed is the master secret, and derives `P`.
///
/// Builds the top tree, `2^12` one-time leaves.
pub fn key_gen(seed: [u8; 32]) -> (SecretKey, PublicKey) {
    let seed = core::array::from_fn(|i| u64::from_le_bytes(seed[8 * i..8 * i + 8].try_into().unwrap()));
    // `P` is hashed under an all-zero one.
    let public_param = th(&[0; 2], &tweak(TWEAK_PARAMETER, 0, 0, 0, 0), &seed);
    let pp = &public_param;
    // The top tree's 4096 one-time leaves, then its levels, folded in place.
    let mut nodes: [Digest; 1 << HEIGHTS[0]] = core::array::from_fn(|e| {
        public_leaf(
            pp,
            &seed,
            Pos {
                lay: 0,
                tau: 0,
                e: e as u32,
            },
        )
    });
    let mut cache = [[0; 2]; CACHE_LEN];
    for level in 0..HEIGHTS[0] {
        // Level 6 holds 64 nodes: the cache.
        if level == SPLIT_LEVEL {
            cache.copy_from_slice(&nodes[..CACHE_LEN]);
        }
        fold(pp, 0, 0, level, 0, &mut nodes[..1 << (HEIGHTS[0] - level)]);
    }
    let root = nodes[0];
    let sk = SecretKey {
        public_param,
        root,
        master: seed,
        cache,
    };
    (sk, PublicKey { root, public_param })
}

impl SecretKey {
    pub const fn public_key(&self) -> PublicKey {
        PublicKey {
            root: self.root,
            public_param: self.public_param,
        }
    }

    /// `Sign`: deterministic and stateless.
    pub fn sign(&self, message: &Message) -> Result<Signature, SphincsSignError> {
        let (pp, master) = (&self.public_param, &self.master);
        // A digest is admissible when its last index is zero: `2^10` tries on average.
        let (randomizer, idx, u) = (0..MAX_DIGEST_ATTEMPTS)
            .find_map(|trial| {
                // Trial `j`'s randomizer: a hash of the master secret and the message.
                let [s0, s1, s2, s3] = *master;
                let [m0, m1, m2, m3] = *message;
                let randomizer = th(
                    pp,
                    &tweak(TWEAK_RANDOMIZER, 0, 0, trial as u32, 0),
                    &[s0, s1, s2, s3, m0, m1, m2, m3],
                );
                let (idx, u) = message_digest(pp, &self.root, &randomizer, message);
                (u[K - 1] == 0).then_some((randomizer, idx, u))
            })
            .ok_or(SphincsSignError::NoAdmissibleDigest)?;
        // The few-time key the index picks, and its opening at the digest's leaves.
        let (fts_key, fts) = fts::open(pp, master, idx, &u);

        // Bottom layer first: each signs the root of the layer below it.
        let mut signed = fts_key;
        let layer2 = self.sign_layer(idx, 2, &mut signed)?;
        let layer1 = self.sign_layer(idx, 1, &mut signed)?;
        let layer0 = self.sign_layer(idx, 0, &mut signed)?;
        debug_assert_eq!(signed, self.root);
        Ok(Signature {
            randomizer,
            fts,
            layer0,
            layer1,
            layer2,
        })
    }

    /// A layer's signature on a message, which the call replaces by the layer's root.
    fn sign_layer<const HEIGHT: usize>(
        &self,
        idx: u64,
        lay: usize,
        message: &mut Digest,
    ) -> Result<LayerSignature<HEIGHT>, SphincsSignError> {
        let (pp, master, pos) = (&self.public_param, &self.master, Pos::of(idx, lay));
        // The least counter with a codeword: a larger one would reveal a second codeword.
        let (counter, x) = (0..MAX_ENCODING_ATTEMPTS)
            .find_map(|c| ots::encode(pp, pos, message, c as u32).map(|x| (c as u32, x)))
            .ok_or(SphincsSignError::NoAdmissibleEncoding)?;
        // Chain `i` opened at value `x_i`.
        let mut chains = ots::Chains::new(pp, pos);
        let ots = core::array::from_fn(|i| chains.walk(i, 0, x.get(i), ots::secret(pp, master, pos, i)));
        // The top layer's tree has the cache; the others are rebuilt whole.
        let mut path = [[0; 2]; HEIGHT];
        *message = if lay == 0 {
            self.top_path(pos.e, &mut path)
        } else {
            self.tree_path(pos, &mut path)
        };
        Ok(LayerSignature {
            counter: counter.into(),
            ots,
            path,
        })
    }

    /// A leaf's path in its tree, rebuilt whole, and the tree's root.
    fn tree_path(&self, pos: Pos, path: &mut [Digest]) -> Digest {
        // A lower layer's tree: 128 leaves, in a buffer sized for the largest tree.
        let (pp, leaves) = (&self.public_param, 1 << HEIGHTS[pos.lay]);
        let mut nodes = [[0; 2]; 1 << HEIGHTS[0]];
        for (e, node) in nodes[..leaves].iter_mut().enumerate() {
            *node = public_leaf(pp, &self.master, Pos { e: e as u32, ..pos });
        }
        path_and_root(pp, pos, 0, 0, &mut nodes[..leaves], path)
    }

    /// The top tree's path at a leaf, and its root.
    ///
    /// ```text
    ///   levels 6..12   folded from the 64 cached nodes
    ///   levels 0..6    the 64-leaf subtree holding the leaf, rebuilt
    /// ```
    fn top_path(&self, e: u32, path: &mut [Digest]) -> Digest {
        let (pp, pos) = (&self.public_param, Pos { lay: 0, tau: 0, e });
        // The subtree's first leaf: the leaf with its low 6 bits cleared.
        let first = e >> SPLIT_LEVEL << SPLIT_LEVEL;
        let mut nodes: [Digest; 1 << SPLIT_LEVEL] = core::array::from_fn(|i| {
            public_leaf(
                pp,
                &self.master,
                Pos {
                    e: first + i as u32,
                    ..pos
                },
            )
        });
        let (below, above) = path.split_at_mut(SPLIT_LEVEL);
        let subtree = path_and_root(pp, pos, 0, u64::from(first), &mut nodes, below);
        // The subtree's root is the cached node above it.
        debug_assert_eq!(subtree, self.cache[(e >> SPLIT_LEVEL) as usize]);
        path_and_root(pp, pos, SPLIT_LEVEL, 0, &mut self.cache.clone(), above)
    }
}

/// The leaf of a one-time key: every chain walked to its end.
fn public_leaf(pp: &PublicParam, master: &[u64; 4], pos: Pos) -> Digest {
    let mut chains = ots::Chains::new(pp, pos);
    ots::leaf_hash(pp, pos, |i| {
        chains.walk(i, 0, CHAIN_LEN - 1, ots::secret(pp, master, pos, i))
    })
}

/// Replace a band of nodes at a level by their parents, in place.
///
/// The band starts at index `first`, an even one.
fn fold(pp: &PublicParam, lay: usize, tau: u32, level: usize, first: u64, nodes: &mut [Digest]) {
    let mut hash = NodeHash::new(pp);
    // Parent `j` reads only children `2j` and `2j + 1`, which no earlier parent overwrote.
    for j in 0..nodes.len() / 2 {
        nodes[j] = node(
            &mut hash,
            lay,
            tau,
            level + 1,
            (first >> 1) + j as u64,
            &nodes[2 * j],
            &nodes[2 * j + 1],
        );
    }
}

/// A leaf's siblings from level `from` up, and the root.
///
/// The nodes are the whole band of level `from` under the root, starting at index `first`.
fn path_and_root(
    pp: &PublicParam,
    pos: Pos,
    from: usize,
    first: u64,
    nodes: &mut [Digest],
    path: &mut [Digest],
) -> Digest {
    let width = nodes.len();
    for (k, sibling) in path.iter_mut().enumerate() {
        // At level `from + k` the band starts at `first >> k` and is `width >> k` wide.
        let level = from + k;
        // The sibling flips the low bit of the leaf's ancestor.
        *sibling = nodes[(((u64::from(pos.e) >> level) ^ 1) - (first >> k)) as usize];
        fold(pp, pos.lay, pos.tau, level, first >> k, &mut nodes[..width >> k]);
    }
    nodes[0]
}
