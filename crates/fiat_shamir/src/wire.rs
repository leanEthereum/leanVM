//! The proof's one encoding, [`Proof::to_bytes`], and its decoding, which unprunes each Merkle phase.

use std::collections::BTreeMap;

use crate::merkle::{Hash, MerklePath, hash_pair, hash_words, padded};
use crate::transcript::Proof;
use primitives::field::{F64, F192};

/// The most phases a proof, queries a phase, leaf words and tree height may have: at least the protocol's own, and few
/// enough that hostile bytes unprune to a bounded size. Encoding asserts them, so an honest proof always decodes.
pub const MAX_PHASES: usize = 9;
pub const MAX_QUERIES: usize = 256;
pub const MAX_LEAF_WORDS: usize = 64;
pub const MAX_HEIGHT: usize = 40;

impl Proof {
    /// Every count and size is a little-endian `u32`, every word and query position a little-endian `u64`.
    ///
    /// - The stream: its length, then each element as its three words.
    /// - The number of phases, then each phase pruned: its queries' count and positions, in the order the verifier
    ///   samples them; the tree's height, the leaf width, and the row width; the leaf at each distinct position,
    ///   ascending, as its last row-width words, the ones before being zero in every leaf of the phase; then the
    ///   siblings no other path's node gives, bottom level first and left to right within a level.
    ///
    /// The row width is the least that drops only zeros, and the sibling count follows from the positions.
    ///
    /// # Panics
    ///
    /// On a proof no prover makes, such as one with an empty phase, or with more phases, queries, leaf words or tree
    /// levels than decoding accepts.
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
    assert!(!paths.is_empty(), "a Merkle phase opens at least one path");
    let (height, leaf_words) = (paths[0].siblings.len(), paths[0].leaf.len());
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
        out.extend(path.leaf_index.to_le_bytes());
    }
    for size in [height, leaf_words, leaf_words - zeros] {
        write_u32(out, size);
    }
    for path in &distinct {
        out.extend(path.leaf[zeros..].iter().flat_map(|word| word.0.to_le_bytes()));
    }
    for level in 0..height {
        let mut nodes: Vec<(u64, Hash)> = distinct
            .iter()
            .map(|path| (path.leaf_index >> level, path.siblings[level]))
            .collect();
        nodes.dedup_by_key(|&mut (node, _)| node);
        for &(node, sibling) in &nodes {
            if nodes.binary_search_by_key(&(node ^ 1), |&(node, _)| node).is_err() {
                out.extend(sibling);
            }
        }
    }
}

/// Unprune a phase's octopus back into its paths, hashing the nodes they share. Nothing is authenticated here, the
/// verifier checks every path; what is refused is anything but the one encoding of a phase within the bounds.
fn read_phase(input: &mut Reader) -> Option<Vec<MerklePath>> {
    let count = input.u32().filter(|&count| count as usize <= MAX_QUERIES)?;
    let queries: Vec<u64> = (0..count).map(|_| input.u64()).collect::<Option<_>>()?;
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
    for level in 0..height {
        let mut siblings = BTreeMap::new();
        let mut parents = BTreeMap::new();
        for (&p, node) in &nodes {
            let sibling = match nodes.get(&(p ^ 1)) {
                Some(&sibling) => sibling,
                None => input.hash()?,
            };
            siblings.insert(p, sibling);
            let (left, right) = if p & 1 == 0 { (node, &sibling) } else { (&sibling, node) };
            parents.entry(p >> 1).or_insert_with(|| hash_pair(left, right));
        }
        for path in &mut distinct {
            path.siblings.push(siblings[&(path.leaf_index >> level)]);
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

    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(*self.bytes(8)?.as_array()?))
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
        let rows = [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]].map(|row| row.map(F64));
        let leaf = |q: usize| hash_words(&rows[q]);
        let node = |level: usize, i: usize| match level {
            0 => leaf(i),
            _ => hash_pair(&leaf(2 * i), &leaf(2 * i + 1)),
        };
        let proof = Proof {
            stream: vec![F192::new(1, 2, 3)],
            merkle: vec![open(4, &[3, 1, 3], 3, node, |q| &rows[q])],
        };
        let bytes = proof.to_bytes();
        // The stream, then the phase: its queries, three sizes, two rows of two words, and two siblings.
        assert_eq!(bytes.len(), (4 + 24) + 4 + (4 + 3 * 8) + 3 * 4 + 2 * 2 * 8 + 2 * 32);
        assert_eq!(Proof::from_bytes(&bytes), Some(proof));
        assert_eq!(Proof::from_bytes(&[&bytes[..], &[0]].concat()), None);
    }
}
