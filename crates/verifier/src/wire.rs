//! The proof's one encoding, [`Proof::to_bytes`], and its decoding, which unprunes each Merkle phase.

use crate::field::{E, K};
use crate::merkle::{MerklePath, hash_leaf, hash_pair};
use crate::transcript::Proof;

/// The most phases a proof, queries a phase, leaf words and tree height may have: at least the protocol's own, and few
/// enough that hostile bytes unprune to a bounded size. Encoding asserts them, so an honest proof always decodes.
pub const MAX_PHASES: usize = 8;
pub const MAX_QUERIES: usize = 256;
pub const MAX_LEAF_WORDS: usize = 64;
pub const MAX_HEIGHT: usize = 32;

impl Proof {
    /// Every count and size is a little-endian `u32`, every word a little-endian `u64`.
    ///
    /// - The stream: its length, then each element as its two words.
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
        let mut out = Vec::new();
        self.write_bytes(&mut out);
        out
    }

    /// [`Self::to_bytes`] appended to `out`.
    ///
    /// # Panics
    ///
    /// As [`Self::to_bytes`].
    pub fn write_bytes(&self, out: &mut Vec<u8>) {
        assert!(self.merkle_openings.len() <= MAX_PHASES);
        write_u32(out, self.stream.len());
        for element in &self.stream {
            out.extend_from_slice(&element.c0.to_le_bytes());
            out.extend_from_slice(&element.c1.to_le_bytes());
        }
        write_u32(out, self.merkle_openings.len());
        for phase in &self.merkle_openings {
            write_phase(out, phase);
        }
    }

    /// The proof `bytes` encode, or `None` unless they are exactly one proof's encoding. Nothing is verified.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut input = Reader(bytes);
        let length = input.u32()? as usize;
        let words = input.words(length.checked_mul(2)?)?;
        let stream = words.as_chunks().0.iter().map(|[c0, c1]| E::new(c0.0, c1.0)).collect();
        let phases = input.u32().filter(|&phases| phases as usize <= MAX_PHASES)?;
        let mut merkle_openings = Vec::new();
        for _ in 0..phases {
            merkle_openings.push(read_phase(&mut input)?);
        }
        input.0.is_empty().then_some(Self {
            stream,
            merkle_openings,
        })
    }
}

/// Prune a phase into its octopus: the fewest siblings that authenticate all its paths together, a sibling being left
/// out where another path's node gives it. No hashing.
fn write_phase(out: &mut Vec<u8>, paths: &[MerklePath]) {
    assert!(!paths.is_empty(), "a Merkle phase opens at least one path");
    let (height, leaf_words) = (paths[0].siblings.len(), paths[0].leaf.len());
    assert!(paths.len() <= MAX_QUERIES && leaf_words <= MAX_LEAF_WORDS && height <= MAX_HEIGHT);
    // The first path at each position, in order of position.
    let mut distinct: Vec<&MerklePath> = Vec::new();
    for path in paths {
        if let Err(at) = distinct.binary_search_by_key(&path.leaf_index, |p| p.leaf_index) {
            distinct.insert(at, path);
        }
    }
    let zeros = distinct
        .iter()
        .map(|path| path.leaf.iter().take_while(|word| word.0 == 0).count())
        .min()
        .unwrap_or(0);

    write_u32(out, paths.len());
    for path in paths {
        write_u32(out, usize::try_from(path.leaf_index).expect("a position fits in usize"));
    }
    write_u32(out, height);
    write_u32(out, leaf_words);
    write_u32(out, leaf_words - zeros);
    for path in &distinct {
        for word in &path.leaf[zeros..] {
            out.extend_from_slice(&word.to_bytes());
        }
    }
    for level in 0..height {
        let mut nodes: Vec<(u64, [u8; 32])> = distinct
            .iter()
            .map(|path| (path.leaf_index >> level, path.siblings[level]))
            .collect();
        nodes.dedup_by_key(|&mut (node, _)| node);
        for &(node, sibling) in &nodes {
            if nodes.binary_search_by_key(&(node ^ 1), |&(node, _)| node).is_err() {
                out.extend_from_slice(&sibling);
            }
        }
    }
}

/// Unprune a phase's octopus back into its paths, hashing the nodes they share. Nothing is authenticated here, the
/// verifier checks every path; what is refused is anything but the one encoding of a phase within the bounds.
fn read_phase(input: &mut Reader) -> Option<Vec<MerklePath>> {
    let count = input.u32().filter(|&count| count as usize <= MAX_QUERIES)?;
    let mut queries = Vec::with_capacity(count as usize);
    for _ in 0..count {
        queries.push(u64::from(input.u32()?));
    }
    let (height, leaf_words, row_words) = (input.u32()? as usize, input.u32()? as usize, input.u32()? as usize);
    let mut positions: Vec<u64> = Vec::new();
    for &query in &queries {
        if let Err(at) = positions.binary_search(&query) {
            positions.insert(at, query);
        }
    }
    if !(height <= MAX_HEIGHT
        && leaf_words <= MAX_LEAF_WORDS
        && row_words <= leaf_words
        && positions.last().is_some_and(|&last| last >> height == 0))
    {
        return None;
    }
    let mut distinct = Vec::with_capacity(positions.len());
    for &leaf_index in &positions {
        let mut leaf = vec![K(0); leaf_words - row_words];
        leaf.extend(input.words(row_words)?);
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

    // Level by level, the nodes the paths climb through, in order of position.
    let mut nodes: Vec<(u64, [u8; 32])> = distinct
        .iter()
        .map(|path| (path.leaf_index, hash_leaf(&path.leaf).0))
        .collect();
    let at = |nodes: &[(u64, [u8; 32])], p: u64| nodes.binary_search_by_key(&p, |&(q, _)| q);
    for level in 0..height {
        let mut siblings = Vec::with_capacity(nodes.len());
        let mut parents: Vec<(u64, [u8; 32])> = Vec::with_capacity(nodes.len());
        for &(p, node) in &nodes {
            let sibling = match at(&nodes, p ^ 1) {
                Ok(i) => nodes[i].1,
                Err(_) => input.hash()?,
            };
            siblings.push(sibling);
            // A pair's two nodes are consecutive, so its parent is the last one pushed.
            if parents.last().is_none_or(|&(q, _)| q != p >> 1) {
                let (left, right) = if p & 1 == 0 {
                    (&node, &sibling)
                } else {
                    (&sibling, &node)
                };
                parents.push((p >> 1, hash_pair(left, right).0));
            }
        }
        for path in &mut distinct {
            let i = at(&nodes, path.leaf_index >> level).expect("a path climbs through a node");
            path.siblings.push(siblings[i]);
        }
        nodes = parents;
    }
    let path = |query: &u64| distinct[positions.binary_search(query).expect("a query is a position")].clone();
    Some(queries.iter().map(path).collect())
}

fn write_u32(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&u32::try_from(value).expect("fits in u32").to_le_bytes());
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

    fn hash(&mut self) -> Option<[u8; 32]> {
        Some(*self.bytes(32)?.as_array()?)
    }

    fn words(&mut self, count: usize) -> Option<Vec<K>> {
        let bytes = self.bytes(count.checked_mul(8)?)?;
        Some(
            bytes
                .as_chunks()
                .0
                .iter()
                .map(|&word| K(u64::from_le_bytes(word)))
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A proof survives its encoding, which carries each leaf without the zero words every opened leaf starts with,
    /// and nothing else decodes to it.
    #[test]
    fn proof_round_trips_through_its_one_encoding() {
        let rows = [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]].map(|row| row.map(K));
        let leaves = rows.map(|row| hash_leaf(&row).0);
        let parents = [hash_pair(&leaves[0], &leaves[1]).0, hash_pair(&leaves[2], &leaves[3]).0];
        let path = |q: usize| MerklePath {
            leaf_index: q as u64,
            leaf: rows[q].to_vec(),
            siblings: vec![leaves[q ^ 1], parents[(q / 2) ^ 1]],
        };
        let proof = Proof {
            stream: vec![E::new(1, 2)],
            merkle_openings: vec![vec![path(3), path(1), path(3)]],
        };
        let bytes = proof.to_bytes();
        // The stream, then the phase: its queries, three sizes, two rows of two words, and two siblings.
        assert_eq!(bytes.len(), (4 + 16) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 2 * 32);
        assert_eq!(Proof::from_bytes(&bytes), Some(proof));
        assert_eq!(Proof::from_bytes(&[&bytes[..], &[0]].concat()), None);
    }
}
