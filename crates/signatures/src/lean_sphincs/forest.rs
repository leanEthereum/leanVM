//! The few-time signature: a two-level forest of small WOTS keys.
//!
//! A forest is `FOREST_TREES` Merkle trees of height `TREE_HEIGHT`. Each leaf of
//! a tree hashes two subtrees of height `SUBTREE_HEIGHT`, whose leaves are WOTS
//! keys of `FOREST_CHAINS` chains. The message digest picks, in each tree, a
//! leaf, and in both of its subtrees a WOTS key and a codeword for it. No tree
//! and no subtree has a root hash: what stands for a root is the two nodes below
//! it, so the last element of a path is the top node the verifier does not
//! compute.
//!
//! A codeword is `FOREST_CHAINS` digits in `0..=4` summing to `CODEWORD_SUM`:
//! the chain is opened that many steps below its top, so the fixed sum is the
//! checksum, and a verifier always walks `CODEWORD_SUM` steps per WOTS key.
//! Reuse leaks rather than breaks: a forgery needs, in every tree, both target
//! WOTS keys already opened at codewords whose componentwise maximum covers the
//! target's.

use crate::lean_sphincs::*;

/// Distinct codewords in the table.
const TABLE_CODEWORDS: usize = 214;

/// The codeword table, entry `t` being the codeword of digest field `t`: the
/// base-5 number whose most significant digit is chain 0's. The 246 codewords, in
/// increasing order, are stably sorted by decreasing sum of squared digits, and
/// entry `t` is number `t mod 214`: the 32 most spread-out ones are left out and
/// the 42 most concentrated appear twice, which is what the lifetime wants
/// (`doc/lean_sphincs`).
const CODEWORDS: [u16; 1 << CODEWORD_BITS] = {
    // The codewords in increasing order, with their sums of squared digits.
    let (mut words, mut squares) = ([0u16; 246], [0usize; 246]);
    let (mut n, mut code) = (0, 0);
    while code < 5usize.pow(FOREST_CHAINS as u32) {
        let (mut sum, mut sum_sq, mut rest) = (0, 0, code);
        while rest > 0 {
            (sum, sum_sq, rest) = (sum + rest % 5, sum_sq + (rest % 5) * (rest % 5), rest / 5);
        }
        if sum == CODEWORD_SUM {
            (words[n], squares[n]) = (code as u16, sum_sq);
            n += 1;
        }
        code += 1;
    }
    assert!(n == words.len());
    let mut sorted = [0u16; TABLE_CODEWORDS];
    let (mut len, mut target) = (0, CODEWORD_SUM * CODEWORD_SUM);
    while len < TABLE_CODEWORDS {
        let mut i = 0;
        while i < n && len < TABLE_CODEWORDS {
            if squares[i] == target {
                sorted[len] = words[i];
                len += 1;
            }
            i += 1;
        }
        target -= 1;
    }
    let mut table = [0; 1 << CODEWORD_BITS];
    let mut t = 0;
    while t < table.len() {
        table[t] = sorted[t % TABLE_CODEWORDS];
        t += 1;
    }
    table
};

pub type Codeword = [u8; FOREST_CHAINS];

/// The codeword of digest field `t`.
pub const fn codeword(t: usize) -> Codeword {
    let mut digits = [0; FOREST_CHAINS];
    let mut code = CODEWORDS[t];
    let mut i = FOREST_CHAINS;
    while i > 0 {
        i -= 1;
        digits[i] = (code % 5) as u8;
        code /= 5;
    }
    digits
}

/// What the digest picks in one tree: a leaf, and in each of its two subtrees a
/// WOTS key and the table index of a codeword.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mark {
    pub leaf: usize,
    pub keys: [usize; SUBTREES],
    pub words: [usize; SUBTREES],
}

/// One opened WOTS key: each chain's value `d_i` steps below its top, and the
/// key's path in its subtree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SubtreeOpening {
    pub values: [Digest; FOREST_CHAINS],
    pub path: [Digest; SUBTREE_HEIGHT],
}

/// What a signature carries for one tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeOpening {
    pub subtrees: [SubtreeOpening; SUBTREES],
    pub path: [Digest; TREE_HEIGHT],
}

pub type ForestOpening = [TreeOpening; FOREST_TREES];

/// A WOTS key of the forest: instance `idx`, tree `c`, leaf `s`, subtree `j`,
/// key `a`.
#[derive(Clone, Copy)]
struct KeyPos {
    idx: u32,
    c: usize,
    s: usize,
    j: usize,
    a: usize,
}

/// What leaf `s` of a tree adds to the `hi` field of the addresses below it.
pub const fn leaf_field(s: usize) -> u32 {
    8 * s as u32
}

/// What WOTS key `a` of a subtree adds to the `hi` field of its addresses.
pub const fn key_field(a: usize) -> u32 {
    256 * a as u32
}

impl KeyPos {
    /// `c + 8 s + 128 j`: the subtree within the instance.
    fn subtree(&self) -> u32 {
        self.c as u32 + leaf_field(self.s) + 128 * self.j as u32
    }

    /// `c + 8 s + 128 j + 256 a`: the key within the instance.
    fn slot(&self) -> u32 {
        self.subtree() + key_field(self.a)
    }

    /// The starts of the key's chains: chains `2t` and `2t + 1` are the two
    /// halves of one hash of the seed.
    fn secrets(&self, pp: &PublicParam, master: &MasterSecret) -> [Digest; FOREST_CHAINS] {
        let mut secrets = [[0u8; N]; FOREST_CHAINS];
        for (t, pair) in secrets.as_chunks_mut::<2>().0.iter_mut().enumerate() {
            let tw = tweak(TWEAK_FOREST_PRF, self.slot() + 2048 * t as u32, self.idx);
            *pair = th_pair(pp, &tw, master);
        }
        secrets
    }

    /// `steps` steps of chain `i` from position `start`; a step carries the
    /// position it leaves.
    fn chain(&self, pp: &PublicParam, i: usize, start: usize, steps: usize, value: Digest) -> Digest {
        debug_assert!(start + steps <= FOREST_CHAIN_TOP);
        let tw = tweak(TWEAK_FOREST_CHAIN, self.slot() + 2048 * i as u32, self.idx);
        (start..start + steps).fold(value, |current, from| th(pp, &tw.step(from), &current))
    }

    /// The subtree leaf of the key: `Th` over its chain tops.
    fn leaf(&self, pp: &PublicParam, tops: &[Digest; FOREST_CHAINS]) -> Digest {
        th_digests(pp, &tweak(TWEAK_FOREST_KEY_LEAF, self.slot(), self.idx), tops)
    }

    fn subtree_node(&self, pp: &PublicParam, level: usize, node: usize, children: &[Digest; 2]) -> Digest {
        let hi = self.subtree() + (256 * level + 1024 * node) as u32;
        th_digests(pp, &tweak(TWEAK_FOREST_SUBNODE, hi, self.idx), children)
    }
}

/// A tree leaf: `Th` over the two top nodes of each of its subtrees.
fn tree_leaf(pp: &PublicParam, idx: u32, c: usize, s: usize, tops: &[[Digest; 2]; SUBTREES]) -> Digest {
    th_digests(
        pp,
        &tweak(TWEAK_FOREST_TREE_LEAF, c as u32 + leaf_field(s), idx),
        tops.as_flattened(),
    )
}

fn tree_node(pp: &PublicParam, idx: u32, c: usize, level: usize, node: usize, children: &[Digest; 2]) -> Digest {
    let hi = (c + 8 * level + 64 * node) as u32;
    th_digests(pp, &tweak(TWEAK_FOREST_NODE, hi, idx), children)
}

/// The few-time public key: `Th` over the two top nodes of every tree.
fn forest_key(pp: &PublicParam, idx: u32, tops: &[[Digest; 2]; FOREST_TREES]) -> Digest {
    th_digests(pp, &tweak(TWEAK_FOREST_KEY, 0, idx), tops.as_flattened())
}

/// The levels of a Merkle tree from its leaves up to its two top nodes.
fn levels(leaves: Vec<Digest>, node: impl Fn(usize, usize, &[Digest; 2]) -> Digest) -> Vec<Vec<Digest>> {
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 2 {
        let level = levels.len();
        let (pairs, _) = levels[level - 1].as_chunks::<2>();
        let up = pairs.iter().enumerate().map(|(j, pair)| node(level, j, pair)).collect();
        levels.push(up);
    }
    levels
}

/// The path of leaf `at`: its sibling on every level, the last being the other
/// top node.
fn path<const HEIGHT: usize>(levels: &[Vec<Digest>], at: usize) -> [Digest; HEIGHT] {
    std::array::from_fn(|level| levels[level][(at >> level) ^ 1])
}

/// A node and its sibling in index order: `bit` says the node is the right one.
fn ordered(bit: usize, node: Digest, sibling: Digest) -> [Digest; 2] {
    if bit & 1 == 0 { [node, sibling] } else { [sibling, node] }
}

/// The two top nodes a leaf at `at` and its path reach.
fn fold(leaf: Digest, at: usize, path: &[Digest], node: impl Fn(usize, usize, &[Digest; 2]) -> Digest) -> [Digest; 2] {
    let (last, below) = path.split_last().unwrap();
    let top = below.iter().enumerate().fold(leaf, |current, (level, sibling)| {
        node(level + 1, at >> (level + 1), &ordered(at >> level, current, *sibling))
    });
    ordered(at >> below.len(), top, *last)
}

/// `Fts.key` and `Fts.open` together, the forest of instance `idx` being built
/// once: its public key, and its opening at `marks`.
pub fn forest_open(
    pp: &PublicParam,
    master: &MasterSecret,
    idx: u32,
    marks: &[Mark; FOREST_TREES],
) -> (Digest, ForestOpening) {
    let mut tops = [[[0u8; N]; 2]; FOREST_TREES];
    let opening = std::array::from_fn(|c| {
        let mark = &marks[c];
        let mut opened = [None; SUBTREES];
        let leaves = (0..1 << TREE_HEIGHT)
            .map(|s| {
                let subtree_tops = std::array::from_fn(|j| {
                    let key = |a| KeyPos { idx, c, s, j, a };
                    let leaves = (0..1 << SUBTREE_HEIGHT)
                        .map(|a| {
                            let key = key(a);
                            let secrets = key.secrets(pp, master);
                            let tops = std::array::from_fn(|i| key.chain(pp, i, 0, FOREST_CHAIN_TOP, secrets[i]));
                            key.leaf(pp, &tops)
                        })
                        .collect();
                    let levels = levels(leaves, |level, node, pair| key(0).subtree_node(pp, level, node, pair));
                    if s == mark.leaf {
                        let key = key(mark.keys[j]);
                        let (secrets, word) = (key.secrets(pp, master), codeword(mark.words[j]));
                        opened[j] = Some(SubtreeOpening {
                            values: std::array::from_fn(|i| {
                                key.chain(pp, i, 0, FOREST_CHAIN_TOP - word[i] as usize, secrets[i])
                            }),
                            path: path(&levels, mark.keys[j]),
                        });
                    }
                    [levels[SUBTREE_HEIGHT - 1][0], levels[SUBTREE_HEIGHT - 1][1]]
                });
                tree_leaf(pp, idx, c, s, &subtree_tops)
            })
            .collect();
        let levels = levels(leaves, |level, node, pair| tree_node(pp, idx, c, level, node, pair));
        tops[c] = [levels[TREE_HEIGHT - 1][0], levels[TREE_HEIGHT - 1][1]];
        TreeOpening {
            subtrees: opened.map(Option::unwrap),
            path: path(&levels, mark.leaf),
        }
    });
    (forest_key(pp, idx, &tops), opening)
}

/// `Fts.recover`: the few-time key an opening reaches at `marks`.
pub fn forest_recover(pp: &PublicParam, idx: u32, marks: &[Mark; FOREST_TREES], opening: &ForestOpening) -> Digest {
    let tops = std::array::from_fn(|c| {
        let (mark, tree) = (&marks[c], &opening[c]);
        let s = mark.leaf;
        let subtree_tops = std::array::from_fn(|j| {
            let (key, sub) = (
                KeyPos {
                    idx,
                    c,
                    s,
                    j,
                    a: mark.keys[j],
                },
                &tree.subtrees[j],
            );
            let word = codeword(mark.words[j]);
            let tops = std::array::from_fn(|i| {
                let steps = word[i] as usize;
                key.chain(pp, i, FOREST_CHAIN_TOP - steps, steps, sub.values[i])
            });
            fold(key.leaf(pp, &tops), key.a, &sub.path, |level, node, pair| {
                key.subtree_node(pp, level, node, pair)
            })
        });
        let leaf = tree_leaf(pp, idx, c, s, &subtree_tops);
        fold(leaf, s, &tree.path, |level, node, pair| {
            tree_node(pp, idx, c, level, node, pair)
        })
    });
    forest_key(pp, idx, &tops)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_codeword_sums_to_the_fixed_sum() {
        for t in 0..1 << CODEWORD_BITS {
            let word = codeword(t);
            assert!(word.iter().all(|&digit| digit as usize <= FOREST_CHAIN_TOP));
            assert_eq!(word.iter().map(|&digit| digit as usize).sum::<usize>(), CODEWORD_SUM);
        }
    }
}
