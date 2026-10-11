//! Words and their bits, the `SPLIT` rows, and the views of four words, the `CAST` rows.

use super::Builder;
#[cfg(feature = "circuit-trace")]
use super::list;
use crate::rec::circuit::{Dw, Ew, Kw, Limbs};
use crate::rec::clean::{
    CAST_DIGEST as DIGEST, CAST_ELEMENT as ELEMENT, CAST_HALVES as HALVES, CAST_WORDS as WORDS, SPLIT_BITS, SPLIT_WORD,
};
use crate::rec::table::Table;

impl Builder {
    fn split_row(&mut self, word: Kw, bits: &[Kw; 64]) {
        let mut slots = [0; 65];
        slots[SPLIT_WORD] = word.0;
        for (slot, bit) in slots[SPLIT_BITS..].iter_mut().zip(bits) {
            *slot = bit.0;
        }
        self.row(Table::Split, &slots);
    }

    /// The 64 bits of `w`, lowest first, each a `K` wire holding 0 or 1.
    pub fn split(&mut self, w: Kw) -> [Kw; 64] {
        traced!(self, format!("split {}", w.0), self.split_rows(w))
    }

    fn split_rows(&mut self, w: Kw) -> [Kw; 64] {
        let v = self.k(w);
        let bits: [Kw; 64] = std::array::from_fn(|i| self.free_k((v >> i) & 1));
        self.split_row(w, &bits);
        bits
    }

    /// The word whose bits are `bits`, lowest first, the rest zero.
    ///
    /// # Panics
    ///
    /// Panics if there are more than 64 bits.
    pub fn pack(&mut self, bits: &[Kw]) -> Kw {
        traced!(
            self,
            format!("pack {}", list(bits.iter().map(|w| w.0))),
            self.pack_rows(bits)
        )
    }

    fn pack_rows(&mut self, bits: &[Kw]) -> Kw {
        assert!(bits.len() <= 64, "a word has 64 bits");
        let zero = self.k_zero();
        let all: [Kw; 64] = std::array::from_fn(|i| bits.get(i).copied().unwrap_or(zero));
        let v = (all.iter().enumerate()).fold(0u64, |acc, (i, &b)| acc | (self.k(b) & 1) << i);
        let w = self.free_k(v);
        self.split_row(w, &all);
        w
    }

    /// A cast row over the words `v`: the given `(slot, wire)` pairs, fresh wires in the other slots.
    fn cast_row(&mut self, given: &[(usize, u32)], v: Limbs) -> [u32; 8] {
        let mut values: [Limbs; 8] = [[0; 4]; 8];
        values[DIGEST] = v;
        values[ELEMENT] = [v[0], v[1], v[2], 0];
        values[HALVES] = [v[0], v[1], 0, 0];
        values[HALVES + 1] = [v[2], v[3], 0, 0];
        for (i, &w) in v.iter().enumerate() {
            values[WORDS + i] = [w, 0, 0, 0];
        }
        let kinds = Table::Cast.slot_kinds();
        let wires: [u32; 8] = std::array::from_fn(|s| {
            (given.iter().find(|&&(at, _)| at == s)).map_or_else(|| self.wire(kinds[s], values[s]), |&(_, w)| w)
        });
        if given.iter().any(|&(s, w)| self.values[w as usize] != values[s]) {
            self.fail("cast");
        }
        self.row(Table::Cast, &wires);
        wires
    }

    /// The limbs of `e`.
    pub fn e_to_k(&mut self, e: Ew) -> [Kw; 3] {
        traced!(self, format!("e_to_k {}", e.0), self.e_to_k_rows(e))
    }

    fn e_to_k_rows(&mut self, e: Ew) -> [Kw; 3] {
        let v = self.e(e);
        let w = self.cast_row(&[(ELEMENT, e.0)], [v.c0, v.c1, v.c2, 0]);
        std::array::from_fn(|i| Kw(w[WORDS + i]))
    }

    /// The element with limbs `k`.
    pub fn k_to_e(&mut self, k: [Kw; 3]) -> Ew {
        traced!(
            self,
            format!("k_to_e {} {} {}", k[0].0, k[1].0, k[2].0),
            self.k_to_e_rows(k)
        )
    }

    fn k_to_e_rows(&mut self, k: [Kw; 3]) -> Ew {
        let v = [self.k(k[0]), self.k(k[1]), self.k(k[2]), 0];
        let given: [(usize, u32); 3] = std::array::from_fn(|i| (WORDS + i, k[i].0));
        Ew(self.cast_row(&given, v)[ELEMENT])
    }

    /// `k` in `E`.
    pub fn k_to_e1(&mut self, k: Kw) -> Ew {
        traced!(self, format!("k_to_e1 {}", k.0), self.k_to_e1_rows(k))
    }

    fn k_to_e1_rows(&mut self, k: Kw) -> Ew {
        let zero = self.k_zero();
        self.k_to_e([k, zero, zero])
    }

    /// A digest's words.
    pub fn d_to_k(&mut self, d: Dw) -> [Kw; 4] {
        traced!(self, format!("d_to_k {}", d.0), self.d_to_k_rows(d))
    }

    fn d_to_k_rows(&mut self, d: Dw) -> [Kw; 4] {
        let v = self.d(d);
        let w = self.cast_row(&[(DIGEST, d.0)], v);
        std::array::from_fn(|i| Kw(w[WORDS + i]))
    }

    /// A digest's first three words as an element, and its last word.
    pub fn d_to_e_and_k(&mut self, d: Dw) -> (Ew, Kw) {
        traced!(self, format!("d_to_e_and_k {}", d.0), self.d_to_e_and_k_rows(d))
    }

    fn d_to_e_and_k_rows(&mut self, d: Dw) -> (Ew, Kw) {
        let v = self.d(d);
        let w = self.cast_row(&[(DIGEST, d.0)], v);
        (Ew(w[ELEMENT]), Kw(w[WORDS + 3]))
    }

    /// The digest whose two 128-bit halves are `lo` and `hi`, each with a zero top limb.
    pub fn halves_to_d(&mut self, lo: Ew, hi: Ew) -> Dw {
        traced!(
            self,
            format!("halves_to_d {} {}", lo.0, hi.0),
            self.halves_to_d_rows(lo, hi)
        )
    }

    fn halves_to_d_rows(&mut self, lo: Ew, hi: Ew) -> Dw {
        let (l, h) = (self.e(lo), self.e(hi));
        if l.c2 != 0 || h.c2 != 0 {
            self.fail("a digest half has a top limb");
        }
        let w = self.cast_row(&[(HALVES, lo.0), (HALVES + 1, hi.0)], [l.c0, l.c1, h.c0, h.c1]);
        Dw(w[DIGEST])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Builder {
        pub(crate) fn k_to_d(&mut self, k: [Kw; 4]) -> Dw {
            let v = k.map(|w| self.k(w));
            let given: [(usize, u32); 4] = std::array::from_fn(|i| (WORDS + i, k[i].0));
            Dw(self.cast_row(&given, v)[DIGEST])
        }
    }
}
