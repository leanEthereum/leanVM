//! Hashing: one `HASH` row per compression, a transcript step, a Merkle node or a block of a long message.

use super::Builder;
use crate::rec::circuit::{Compression, Dw, Ew, Kw, Limbs, PARAM_IV};
use crate::rec::table::Table;
use crate::rv::Hash;
use primitives::field::F192;

/// Input wires of one hash row, before its output and individual message-word slots.
#[derive(Clone, Copy)]
struct HashHead {
    /// Input chaining value.
    h: Dw,

    /// Byte counter and finalization flag, followed by two zero words.
    tf: Dw,

    /// Four-word message half selected by the Merkle path bit.
    mux: Dw,

    /// Selects the left message half when zero and the right half when one.
    bit: Kw,

    /// Message words four through six, packed as an extension-field element.
    x: Ew,

    /// Final message word.
    ds: Kw,
}

impl Builder {
    /// Ordinary one-block BLAKE2s on `acc || x || ds`, from the parameter IV.
    ///
    /// Returns the digest and its first three words.
    pub fn compress(&mut self, acc: Dw, x: Ew, ds: Kw) -> (Dw, Ew) {
        let bit = self.k_zero();
        let (a, xv, dv) = (self.d(acc), self.e(x), self.k(ds));
        let m = [a[0], a[1], a[2], a[3], xv.c0, xv.c1, xv.c2, dv];
        self.single_block(acc, bit, x, ds, m)
    }

    /// One Merkle node: the parent of `acc` and `sibling`, `acc` on the right if `bit` is set.
    pub fn node(&mut self, acc: Dw, bit: Kw, sibling: Limbs) -> Dw {
        let a = self.d(acc);
        let (left, right) = if self.k(bit) == 1 { (sibling, a) } else { (a, sibling) };
        let m = [
            left[0], left[1], left[2], left[3], right[0], right[1], right[2], right[3],
        ];
        let x = self.free_e(F192::new(m[4], m[5], m[6]));
        let ds = self.free_k(m[7]);
        self.single_block(acc, bit, x, ds, m).0
    }

    /// One Merkle node over two wired children: the parent of `left` and `right`.
    pub fn parent(&mut self, left: Dw, right: Dw) -> Dw {
        let (l, rv) = (self.d(left), self.d(right));
        let m = [l[0], l[1], l[2], l[3], rv[0], rv[1], rv[2], rv[3]];
        let (x, ds) = self.d_to_e_and_k(right);
        let bit = self.k_zero();
        self.single_block(left, bit, x, ds, m).0
    }

    /// One block of a long message: `m` absorbed into `h` at byte counter `t`, final if `last`.
    pub fn leaf_block(&mut self, h: Dw, m: [Kw; 8], t: u64, last: bool) -> Dw {
        let compression = Compression::new(self.d(h), m.map(|w| self.k(w)), t, last);
        let v = &compression.inputs()[6..];
        let head = HashHead {
            h,
            tf: self.d_const([t, if last { Hash::FINAL } else { 0 }, 0, 0]),
            mux: self.free_d([v[0], v[1], v[2], v[3]]),
            bit: self.free_k(0),
            x: self.free_e(F192::new(v[4], v[5], v[6])),
            ds: self.free_k(v[7]),
        };
        self.hash_row(head, m.map(|w| w.0), compression).0
    }

    /// The hash of `words` in rows, as the native chain computes it.
    pub fn chain(&mut self, words: &[Kw]) -> Dw {
        let n_blocks = words.len().div_ceil(8).max(1);
        let zero = self.k_zero();
        let bytes = 8 * words.len() as u64;
        let mut h = self.d_const(PARAM_IV);
        for j in 0..n_blocks {
            let m: [Kw; 8] = std::array::from_fn(|i| words.get(8 * j + i).copied().unwrap_or(zero));
            h = self.leaf_block(h, m, (64 * (j as u64 + 1)).min(bytes), j + 1 == n_blocks);
        }
        h
    }

    /// A one-block compression from the parameter IV, its message words free but for the mux, `x` and `ds`.
    fn single_block(&mut self, mux: Dw, bit: Kw, x: Ew, ds: Kw, m: [u64; 8]) -> (Dw, Ew) {
        let head = HashHead {
            h: self.d_const(PARAM_IV),
            tf: self.d_const([64, Hash::FINAL, 0, 0]),
            mux,
            bit,
            x,
            ds,
        };
        let words = m.map(|v| self.free_k(v).0);
        self.hash_row(head, words, Compression::single(m))
    }

    /// A hash row: its head's slots, then its output and challenge, then its message's words.
    fn hash_row(&mut self, head: HashHead, words: [u32; 8], compression: Compression) -> (Dw, Ew) {
        let out = compression.output();
        let o = self.free_d(out);
        let ch = self.free_e(F192::new(out[0], out[1], out[2]));
        let HashHead { h, tf, mux, bit, x, ds } = head;
        let mut slots = [0u32; Table::Hash.n_slots()];
        slots[..8].copy_from_slice(&[h.0, tf.0, mux.0, bit.0, x.0, ds.0, o.0, ch.0]);
        slots[8..].copy_from_slice(&words);
        self.row(Table::Hash, &slots);
        self.hash.push(compression);
        (o, ch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rec::circuit::{chain, digest_limbs};
    use fiat_shamir::arith::{Native, Portable};

    #[test]
    fn the_chain_in_rows_is_the_native_chain() {
        for n in [0, 3, 8, 13, 16] {
            let words: Vec<u64> = (0..n).map(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i + 1)).collect();
            let mut b = Builder::new();
            let wires: Vec<Kw> = words.iter().map(|&w| b.free_k(w)).collect();
            let h = b.chain(&wires);
            assert_eq!(b.d(h), chain::<Portable>(&words), "{n} words");
            assert_eq!(chain::<Native>(&words), chain::<Portable>(&words), "{n} words");
            // The native chain is BLAKE2s of the words' bytes, so its length is hashed.
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
            assert_eq!(
                chain::<Portable>(&words),
                digest_limbs(&primitives::hash::hash(&bytes)),
                "{n} words"
            );
        }
    }
}
