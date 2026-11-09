//! The plain rendering of a proof, which hashes nothing and prunes nothing: every count a
//! little-endian `u32`, every word and position a little-endian `u64`, a scalar three words
//! `c0, c1, c2`; the Merkle openings the phase count, and per phase its path count, and per path
//! its position, its leaf's length and words, its siblings' count and their 32 bytes each.
//! `merkle_phases.bin` is the openings alone. Shared by `leanvm-rust-verify` and, through
//! `#[path]`, `leanvm-rust-wire`.

pub struct Reader<'a>(pub &'a [u8]);

impl<'a> Reader<'a> {
    pub fn bytes(&mut self, length: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(length)?;
        self.0 = rest;
        Some(head)
    }

    pub fn u32(&mut self) -> Option<usize> {
        Some(u32::from_le_bytes(self.bytes(4)?.try_into().ok()?) as usize)
    }

    pub fn u64(&mut self) -> Option<u64> {
        self.bytes(8).map(word)
    }

    /// `count` scalars, as their three words.
    pub fn scalars(&mut self, count: usize) -> Option<Vec<[u64; 3]>> {
        let bytes = self.bytes(count.checked_mul(24)?)?;
        Some(
            bytes
                .chunks_exact(24)
                .map(|scalar| std::array::from_fn(|i| word(&scalar[8 * i..])))
                .collect(),
        )
    }

    /// The Merkle openings, each path built by `path` from its position, leaf and siblings.
    /// Counts are checked against the bytes left before anything is allocated.
    pub fn phases<P>(&mut self, path: impl Fn(u64, Vec<u64>, Vec<[u8; 32]>) -> P) -> Option<Vec<Vec<P>>> {
        let mut phases = Vec::new();
        for _ in 0..self.u32()? {
            let mut phase = Vec::new();
            for _ in 0..self.u32()? {
                let leaf_index = self.u64()?;
                let length = self.u32()?;
                let leaf = self.bytes(length.checked_mul(8)?)?.chunks_exact(8).map(word).collect();
                let length = self.u32()?;
                let siblings = self.bytes(length.checked_mul(32)?)?;
                let siblings = siblings
                    .chunks_exact(32)
                    .map(|digest| digest.try_into().expect("32 bytes"))
                    .collect();
                phase.push(path(leaf_index, leaf, siblings));
            }
            phases.push(phase);
        }
        Some(phases)
    }
}

/// The little-endian word of the first eight bytes.
fn word(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes[..8].try_into().expect("eight bytes"))
}
