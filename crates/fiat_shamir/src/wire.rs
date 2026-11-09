//! The proof's one encoding, [`Proof::to_bytes`], and its decoding, which unprunes each Merkle phase.

use std::collections::BTreeMap;

use crate::merkle::{Hash, MerklePath, arity, hash_children, hash_words, levels, padded, sibling_count};
use crate::transcript::Proof;
use primitives::field::{F64, F192};

/// The most phases a proof, queries a phase, leaf words and tree height may have: at least the protocol's own, and few
/// enough that hostile bytes unprune to a bounded size. Encoding asserts them, so an honest proof always decodes.
const MAX_PHASES: usize = 8;
const MAX_QUERIES: usize = 256;
const MAX_LEAF_WORDS: usize = 64;
const MAX_HEIGHT: usize = 32;

impl Proof {
    /// Every count and size is a little-endian `u32`, every word a little-endian `u64`.
    ///
    /// - The stream: its length, then each element as its three words.
    /// - The number of phases, then each phase pruned: its queries' count and positions, in the order the verifier
    ///   samples them; the tree's height in bits, the leaf width, and the row width; the leaf at each distinct
    ///   position, ascending, as its last row-width words, the ones before being zero in every leaf of the phase;
    ///   then the siblings no other path's node gives, bottom level first and left to right within a level.
    ///
    /// The row width is the least that drops only zeros, and the sibling count follows from the positions.
    pub fn to_bytes(&self) -> Vec<u8> {
        assert!(self.merkle.len() <= MAX_PHASES);
        let mut out = Vec::new();
        write_u32(&mut out, self.stream.len());
        for element in &self.stream {
            out.extend(element.to_limbs().map(u64::to_le_bytes).as_flattened());
        }
        write_u32(&mut out, self.merkle.len());
        for phase in &self.merkle {
            write_phase(&mut out, phase);
        }
        out
    }

    /// The proof `bytes` encode, or `None` unless they are exactly one proof's encoding. Nothing is verified.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut input = Reader(bytes);
        let length = input.u32()? as usize;
        let words = input.words(length.checked_mul(3)?)?;
        let stream = words
            .as_chunks()
            .0
            .iter()
            .map(|[c0, c1, c2]| F192::new(c0.0, c1.0, c2.0))
            .collect();
        let phases = input.u32().filter(|&phases| phases as usize <= MAX_PHASES)?;
        let merkle = (0..phases).map(|_| read_phase(&mut input)).collect::<Option<_>>()?;
        input.0.is_empty().then_some(Self { stream, merkle })
    }
}

/// Prune a phase into its octopus: the fewest siblings that authenticate all its paths together, a sibling being left
/// out where another path's node gives it. No hashing.
fn write_phase(out: &mut Vec<u8>, paths: &[MerklePath]) {
    let (count, leaf_words) = (paths[0].siblings.len(), paths[0].leaf.len());
    let height = 2 * (count / 3) + count % 3;
    assert_eq!(sibling_count(height), count, "a path's sibling count");
    assert!(paths.len() <= MAX_QUERIES && leaf_words <= MAX_LEAF_WORDS && height <= MAX_HEIGHT);
    let mut distinct: Vec<&MerklePath> = paths.iter().collect();
    distinct.sort_by_key(|path| path.leaf_index);
    distinct.dedup_by_key(|path| path.leaf_index);
    let zeros = distinct
        .iter()
        .map(|path| path.leaf.iter().take_while(|word| word.0 == 0).count())
        .min()
        .unwrap_or(0);

    write_u32(out, paths.len());
    for path in paths {
        write_u32(out, usize::try_from(path.leaf_index).expect("a position fits in usize"));
    }
    for size in [height, leaf_words, leaf_words - zeros] {
        write_u32(out, size);
    }
    for path in &distinct {
        out.extend(path.leaf[zeros..].iter().flat_map(|word| word.0.to_le_bytes()));
    }
    let mut at = 0;
    for level in 0..levels(height) {
        let arity = arity(height, level);
        let mut nodes: Vec<(u64, &[Hash])> = distinct
            .iter()
            .map(|path| (path.leaf_index >> (2 * level), &path.siblings[at..at + arity - 1]))
            .collect();
        nodes.dedup_by_key(|&mut (node, _)| node);
        // A family's known nodes all carry its other children: the first one's are enough.
        for family in nodes.chunk_by(|a, b| a.0 / arity as u64 == b.0 / arity as u64) {
            let (node, siblings) = family[0];
            let first = node - node % arity as u64;
            let others = (first..first + arity as u64).filter(|&child| child != node);
            for (child, sibling) in others.zip(siblings) {
                if family.binary_search_by_key(&child, |&(node, _)| node).is_err() {
                    out.extend(sibling);
                }
            }
        }
        at += arity - 1;
    }
}

/// Unprune a phase's octopus back into its paths, hashing the nodes they share. Nothing is authenticated here, the
/// verifier checks every path; what is refused is anything but the one encoding of a phase within the bounds.
fn read_phase(input: &mut Reader) -> Option<Vec<MerklePath>> {
    let count = input.u32().filter(|&count| count as usize <= MAX_QUERIES)?;
    let queries: Vec<u64> = (0..count).map(|_| input.u32().map(u64::from)).collect::<Option<_>>()?;
    let (height, leaf_words, row_words) = (input.u32()? as usize, input.u32()? as usize, input.u32()? as usize);
    let mut positions = queries.clone();
    positions.sort_unstable();
    positions.dedup();
    if !(height <= MAX_HEIGHT
        && leaf_words <= MAX_LEAF_WORDS
        && row_words <= leaf_words
        && positions.last().is_some_and(|&last| last >> height == 0))
    {
        return None;
    }
    let mut distinct = Vec::with_capacity(positions.len());
    for &leaf_index in &positions {
        let leaf = padded(&input.words(row_words)?, leaf_words);
        distinct.push(MerklePath {
            leaf_index,
            leaf,
            siblings: Vec::new(),
        });
    }
    // The rows start where the zero words every leaf starts with end.
    if row_words > 0 && distinct.iter().all(|path| path.leaf[leaf_words - row_words].0 == 0) {
        return None;
    }

    // Level by level, the nodes the paths climb through.
    let mut nodes: BTreeMap<u64, Hash> = distinct
        .iter()
        .map(|path| (path.leaf_index, hash_words(&path.leaf)))
        .collect();
    for level in 0..levels(height) {
        let arity = arity(height, level) as u64;
        let mut siblings = BTreeMap::new();
        let mut parents = BTreeMap::new();
        let known: Vec<u64> = nodes.keys().copied().collect();
        for family in known.chunk_by(|a, b| a / arity == b / arity) {
            let first = family[0] - family[0] % arity;
            let children = (first..first + arity)
                .map(|child| nodes.get(&child).copied().or_else(|| input.hash()))
                .collect::<Option<Vec<Hash>>>()?;
            for &node in family {
                let others = (first..).zip(&children).filter(|&(child, _)| child != node);
                siblings.insert(node, others.map(|(_, &hash)| hash).collect::<Vec<_>>());
            }
            parents.insert(first / arity, hash_children(&children));
        }
        for path in &mut distinct {
            path.siblings.extend(&siblings[&(path.leaf_index >> (2 * level))]);
        }
        nodes = parents;
    }
    let path = |query: &u64| distinct[positions.binary_search(query).expect("a query is a position")].clone();
    Some(queries.iter().map(path).collect())
}

fn write_u32(out: &mut Vec<u8>, value: usize) {
    out.extend(u32::try_from(value).expect("fits in u32").to_le_bytes());
}

/// Bytes being decoded, each read refused past their end.
struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    fn bytes(&mut self, length: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(length)?;
        self.0 = rest;
        Some(head)
    }

    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(*self.bytes(4)?.as_array()?))
    }

    fn hash(&mut self) -> Option<Hash> {
        Some(*self.bytes(32)?.as_array()?)
    }

    fn words(&mut self, count: usize) -> Option<Vec<F64>> {
        let bytes = self.bytes(count.checked_mul(8)?)?;
        Some(
            bytes
                .as_chunks()
                .0
                .iter()
                .map(|&word| F64(u64::from_le_bytes(word)))
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::open;

    /// A proof survives its encoding, which carries each leaf without the zero words every opened leaf starts with,
    /// and nothing else decodes to it.
    #[test]
    fn proof_round_trips_through_its_one_encoding() {
        let rows: [[F64; 3]; 8] = std::array::from_fn(|q| [0, q as u64 % 2, q as u64 + 1].map(F64));
        let leaf = |q: usize| hash_words(&rows[q]);
        let node = |level: usize, i: usize| match level {
            0 => leaf(i),
            _ => hash_children(&[leaf(4 * i), leaf(4 * i + 1), leaf(4 * i + 2), leaf(4 * i + 3)]),
        };
        let proof = Proof {
            stream: vec![F192::new(1, 2, 3)],
            merkle: vec![open(8, &[6, 1, 6], 3, node, |q| &rows[q])],
        };
        let bytes = proof.to_bytes();
        // The stream, then the phase: its queries, three sizes, two rows of two words, and the six leaves no path
        // gives; the root's two children are both on a path.
        assert_eq!(bytes.len(), (4 + 24) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 6 * 32);
        assert_eq!(Proof::from_bytes(&bytes), Some(proof));
        assert_eq!(Proof::from_bytes(&[&bytes[..], &[0]].concat()), None);
    }
}
