//! The wire decoder (`NativeVm/Wire/Model.lean`, `decodeM`): the proof's bytes into the decoded
//! area (`input.rs`, `Decoded`), the phases unpruned as the model reads them, each level's
//! carried siblings read while the level climbs.

use crate::input::{MAX_HEIGHT, MAX_LEAF_WORDS, MAX_PHASES, MAX_QUERIES, OPENING_WORDS, phase_base, stream_end};
use crate::keccak::{Digest, hash_pair, hash_words};

/// A node of a level: its position and its digest.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Node {
    pub key: u64,
    pub digest: Digest,
}

/// The decoder's working words (`Wire.workWords`): the queries, the distinct positions, the
/// level's nodes and the next level's, each level's nodes with their siblings, the leaves.
#[repr(C)]
pub struct DecodeWork {
    queries: [u64; MAX_QUERIES],
    positions: [u64; MAX_QUERIES],
    /// The level's nodes and the next level's, alternately.
    nodes: [[Node; MAX_QUERIES]; 2],
    sib_counts: [usize; MAX_HEIGHT],
    sibs: [[Node; MAX_QUERIES]; MAX_HEIGHT],
    leaves: [[u64; MAX_LEAF_WORDS]; MAX_QUERIES],
}

/// The reader: the bytes and a position in them.
#[repr(C)]
struct Reader<'a> {
    bytes: &'a [u8],
    c: usize,
}

impl Reader<'_> {
    /// `leAt`: the little-endian word of the `n ≤ 8` bytes from `c`, which must be there.
    #[inline(never)]
    fn le(&mut self, n: usize) -> Option<u64> {
        let bytes = self.bytes.get(self.c..self.c.checked_add(n)?)?;
        self.c += n;
        Some(bytes.iter().rev().fold(0u64, |w, &b| (w << 8) | u64::from(b)))
    }

    /// `rdU32`.
    #[inline(always)]
    fn u32(&mut self) -> Option<u64> {
        self.le(4)
    }

    /// `rdDigest`.
    #[inline(never)]
    fn digest(&mut self) -> Option<Digest> {
        Some([self.le(8)?, self.le(8)?, self.le(8)?, self.le(8)?])
    }

    /// `rdWords n`: `n` words, all there or none read.
    #[inline(never)]
    fn words(&mut self, out: &mut [u64]) -> Option<()> {
        let end = self.c.checked_add(out.len().checked_mul(8)?)?;
        if end > self.bytes.len() {
            return None;
        }
        for w in out.iter_mut() {
            *w = self.le(8)?;
        }
        Some(())
    }
}

/// `insD`: add `x` to the ascending `sorted[..n]` unless it is there; the new count.
#[inline(never)]
fn ins_d(sorted: &mut [u64; MAX_QUERIES], n: usize, x: u64) -> usize {
    let mut i = 0;
    while i < n && sorted[i % MAX_QUERIES] < x {
        i += 1;
    }
    if i < n && sorted[i % MAX_QUERIES] == x {
        return n;
    }
    let mut j = n.min(MAX_QUERIES - 1);
    while j > i {
        sorted[j % MAX_QUERIES] = sorted[(j - 1) % MAX_QUERIES];
        j -= 1;
    }
    sorted[i % MAX_QUERIES] = x;
    n + 1
}

/// The index of the first node of `key` (`List.lookup` on the nodes).
#[inline(never)]
fn find(nodes: &[Node], key: u64) -> Option<usize> {
    nodes.iter().position(|n| n.key == key)
}

/// `rdRows` with each row `paddedLeaf`: `n` rows of `row_words` words into `leaves`, each after
/// `leaf_words - row_words` zeros; whether every row's first word is zero.
#[inline(never)]
fn rd_rows(
    r: &mut Reader,
    n: usize,
    leaf_words: usize,
    row_words: usize,
    leaves: &mut [[u64; MAX_LEAF_WORDS]; MAX_QUERIES],
) -> Option<bool> {
    let mut all_zero = true;
    for leaf in leaves.get_mut(..n)? {
        let (zeros, row) = leaf.get_mut(..leaf_words)?.split_at_mut_checked(leaf_words.checked_sub(row_words)?)?;
        for z in zeros.iter_mut() {
            *z = 0;
        }
        r.words(row)?;
        all_zero &= row.first().is_none_or(|&x| x == 0);
    }
    Some(all_zero)
}

/// A level of `climbM`: each of the level's `nodes` with its sibling into `sibs` (`sibsM`), and
/// their parents into `next` (`parentsOf`); the parents' count.
#[inline(never)]
fn climb_level(r: &mut Reader, nodes: &[Node], sibs: &mut [Node; MAX_QUERIES], next: &mut [Node; MAX_QUERIES]) -> Option<usize> {
    let mut parents = 0;
    for (i, node) in nodes.iter().enumerate() {
        // `nodes.lookup (v ^^^ 1)`.
        let found = nodes.iter().find(|m| m.key == node.key ^ 1);
        let (digest, carried) = match found {
            Some(m) => (m.digest, false),
            None => (r.digest()?, true),
        };
        *sibs.get_mut(i)? = Node { key: node.key, digest };
        if node.key % 2 == 0 || carried {
            let parent = if node.key % 2 == 0 { hash_pair(&node.digest, &digest) } else { hash_pair(&digest, &node.digest) };
            *next.get_mut(parents)? = Node { key: node.key >> 1, digest: parent };
            parents += 1;
        }
    }
    Some(parents)
}

/// The openings of a phase into `out`: its count, height and leaf width, then each query's
/// position, its leaf (`(positions.zip leaves).lookup q`) and its path (level `l`'s sibling
/// `(sibs l).lookup (q >>> l)`, else zeros).
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn write_openings(
    queries: &[u64],
    positions: &[u64],
    leaves: &[[u64; MAX_LEAF_WORDS]; MAX_QUERIES],
    leaf_words: usize,
    height: usize,
    sibs: &[[Node; MAX_QUERIES]; MAX_HEIGHT],
    sib_counts: &[usize; MAX_HEIGHT],
    out: &mut [u64],
) -> Option<()> {
    let (head, openings) = out.split_at_mut_checked(3)?;
    head.copy_from_slice(&[queries.len() as u64, height as u64, leaf_words as u64]);
    for (j, &q) in queries.iter().enumerate() {
        let o = openings.get_mut(j * OPENING_WORDS..(j + 1) * OPENING_WORDS)?;
        o[0] = q;
        let i = positions.iter().position(|&p| p == q)?;
        for (slot, &x) in o.get_mut(1..1 + leaf_words)?.iter_mut().zip(leaves.get(i)?) {
            *slot = x;
        }
        for level in 0..height {
            let sibs = sibs.get(level)?.get(..*sib_counts.get(level)?)?;
            let digest = find(sibs, q >> level).and_then(|k| sibs.get(k)).map_or([0; 4], |s| s.digest);
            let at = 1 + MAX_LEAF_WORDS + 4 * level;
            for (slot, &x) in o.get_mut(at..at + 4)?.iter_mut().zip(&digest) {
                *slot = x;
            }
        }
    }
    Some(())
}

/// `phaseM`: a phase at the reader's position into the decoded words `out` (`phaseWords` of them).
#[inline(never)]
fn phase_m(r: &mut Reader, out: &mut [u64], w: &mut DecodeWork) -> Option<()> {
    let count = r.u32()?;
    if count > MAX_QUERIES as u64 {
        return None;
    }
    let count = count as usize;
    let queries = w.queries.get_mut(..count)?;
    for q in queries.iter_mut() {
        *q = r.u32()?;
    }
    let height = r.u32()?;
    let leaf_words = r.u32()?;
    let row_words = r.u32()?;
    // `sortD`.
    let mut n = 0;
    for &q in queries.iter() {
        n = ins_d(&mut w.positions, n, q);
    }
    let positions = w.positions.get(..n)?;
    let last = positions.last().copied();
    let ok = height <= MAX_HEIGHT as u64
        && leaf_words <= MAX_LEAF_WORDS as u64
        && row_words <= leaf_words
        && last.is_some_and(|l| l < 1u64 << height);
    if !ok {
        return None;
    }
    let (height, leaf_words, row_words) = (height as usize, leaf_words as usize, row_words as usize);
    let all_zero = rd_rows(r, n, leaf_words, row_words, &mut w.leaves)?;
    if row_words > 0 && all_zero {
        return None;
    }
    for (node, (&p, leaf)) in w.nodes[0].iter_mut().zip(positions.iter().zip(&w.leaves)) {
        *node = Node { key: p, digest: hash_words(leaf.get(..leaf_words)?) };
    }
    // `climbM`: each level's nodes with their siblings, then their parents.
    let mut level_n = n;
    for level in 0..height {
        let [even, odd] = &mut w.nodes;
        let (nodes, next) = if level % 2 == 0 { (&*even, odd) } else { (&*odd, even) };
        let parents = climb_level(r, nodes.get(..level_n)?, w.sibs.get_mut(level)?, next)?;
        *w.sib_counts.get_mut(level)? = level_n;
        level_n = parents;
    }
    write_openings(w.queries.get(..count)?, positions, &w.leaves, leaf_words, height, &w.sibs, &w.sib_counts, out)
}

/// **The model** (`decodeM`): the stream, the phase count, the phases, no byte left; into `dec`.
#[inline(never)]
pub fn decode(bytes: &[u8], dec: &mut [u64], w: &mut DecodeWork) -> Option<()> {
    let l = bytes.len();
    let mut r = Reader { bytes, c: 0 };
    // `streamM`.
    let n = r.u32()? as usize;
    let words = dec.get_mut(1..1 + 2 * n)?;
    r.words(words)?;
    *dec.first_mut()? = n as u64;
    let p = r.u32()?;
    if p > MAX_PHASES as u64 {
        return None;
    }
    *dec.get_mut(stream_end(l))? = p;
    for k in 0..p as usize {
        let base = phase_base(l, k);
        phase_m(&mut r, dec.get_mut(base..phase_base(l, k + 1))?, w)?;
    }
    if r.c != l {
        return None;
    }
    Some(())
}
