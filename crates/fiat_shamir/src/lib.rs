//! Proof transport and a byte-oriented BLAKE2s compression duplex.
//!
//! Absorption maintains a framed chaining value. Domain-separated terminal nodes produce output
//! blocks without exposing that chaining value. Consecutive calls concatenate within each mode;
//! switching back to absorption binds the number of output bytes actually consumed.

pub mod arith;
pub mod merkle;
pub mod transcript;

use primitives::field::{F64, F192};
use std::sync::atomic::{AtomicU64, Ordering};

/// A 32-byte digest as four little-endian field words.
pub fn digest_words(digest: &[u8; 32]) -> [F64; 4] {
    primitives::hash::digest_words(digest).map(F64)
}

/// The logical duplex state captured without hashing, consuming output, or flushing pending input.
///
/// `K` holds a little-endian 64-bit word and `R` holds the chaining value. This is a snapshot, not a constructor for a duplex.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TranscriptContext<K, R> {
    pub state: R,
    /// Only live words are present; the last partial word is zero-padded.
    pub pending: [Option<K>; 8],
    /// The exact live input length, from zero through 64 bytes.
    pub pending_bytes: usize,
    pub first: bool,
    pub previous: u64,
    pub squeezed: u64,
}

/// The seed node, the only leaf in a transcript's compression tree.
pub const SEED: u64 = 1 << 56;
/// An output block. Its result is never a chaining value.
pub const OUTPUT: u64 = 6 << 56;
/// A commitment to the transcript, including its output cursor.
pub const COMMIT: u64 = 7 << 56;
/// A proof-of-work base, separate from live challenges.
pub const POW_BASE: u64 = 8 << 56;
/// An internal node binding a nonce, its difficulty, and the output cursor.
pub const NONCE: u64 = 9 << 56;
/// The last word in the ordinary one-block BLAKE2s proof-of-work input.
pub const POW_TAG: u64 = 0x31574f502d534646;
/// The maximum number of bytes consumed in one uninterrupted squeeze run.
pub const MAX_SQUEEZE_BYTES: u64 = (1 << 49) - 1;
/// Grinding tests a contiguous window of the digest's low word.
pub const MAX_GRINDING_BITS: u32 = 63;

/// The counter word for an absorption node, shared with the row verifier.
///
/// `previous` is the preceding squeeze run's consumed byte count on the first block only.
/// The final block's exact length distinguishes zero padding from message bytes.
///
/// # Panics
///
/// Invalid lengths, noncanonical continuation cursors, and exhausted cursors are refused.
pub const fn absorb_tweak(first: bool, last: bool, len: usize, previous: u64) -> u64 {
    assert!(
        len > 0 && len <= 64 && (last || len == 64),
        "invalid absorb block length"
    );
    assert!(
        previous <= MAX_SQUEEZE_BYTES && (first || previous == 0),
        "invalid absorb cursor"
    );
    let role = match (first, last) {
        (true, false) => 2,
        (false, false) => 3,
        (true, true) => 4,
        (false, true) => 5,
    };
    (role << 56) | ((len as u64) << 49) | previous
}

fn compress_block(mut cv: [u32; 8], block: &[u8; 64], tweak: u64) -> [u32; 8] {
    let words = std::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    primitives::hash::compress(&mut cv, &words, tweak, true);
    cv
}

fn words(cv: [u32; 8]) -> [F64; 4] {
    std::array::from_fn(|i| F64(u64::from(cv[2 * i]) | u64::from(cv[2 * i + 1]) << 32))
}

fn pow_bits_ok(base: [F64; 4], nonce: F192, bits: u32) -> bool {
    let mut input = [0u8; 64];
    let values = [
        base[0].0, base[1].0, base[2].0, base[3].0, nonce.c0, nonce.c1, nonce.c2, POW_TAG,
    ];
    for i in 0..8 {
        input[8 * i..8 * i + 8].copy_from_slice(&values[i].to_le_bytes());
    }
    let digest = primitives::hash::hash(&input);
    u64::from_le_bytes(digest[..8].try_into().unwrap()) & ((1u64 << bits) - 1) == 0
}

/// A reusable byte duplex with bounded, allocation-free buffering.
///
/// Empty calls do nothing. Positive absorb calls concatenate until a positive squeeze or a nonce
/// event. Positive squeeze calls concatenate until absorption or a nonce event. Cloning preserves
/// pending input and unused output bytes; it does not expose an injectable chaining value.
#[derive(Clone)]
pub struct Duplex {
    cv: [u32; 8],
    pending: [u8; 64],
    n_pending: usize,
    first: bool,
    previous: u64,
    squeezed: u64,
    output: [u8; 32],
}

impl Duplex {
    /// Bind both the protocol/domain digest and public-statement digest before any output.
    pub fn new(domain: [F64; 4], statement: [F64; 4]) -> Self {
        let mut input = [0u8; 64];
        for i in 0..4 {
            input[8 * i..8 * i + 8].copy_from_slice(&domain[i].0.to_le_bytes());
        }
        for i in 0..4 {
            input[32 + 8 * i..40 + 8 * i].copy_from_slice(&statement[i].0.to_le_bytes());
        }
        Self {
            cv: compress_block(primitives::hash::PARAM_IV, &input, SEED),
            pending: [0; 64],
            n_pending: 0,
            first: true,
            previous: 0,
            squeezed: 0,
            output: [0; 32],
        }
    }

    /// A labeled protocol with the zero statement digest.
    pub fn from_label(label: &[u8]) -> Self {
        Self::new(digest_words(&primitives::hash::hash(label)), [F64::ZERO; 4])
    }

    /// Capture all logical state without flushing input, hashing, sampling, or allocating.
    ///
    /// For states produced by the private fields and public duplex operations, a live cached output suffix is determined by the chaining value and squeeze cursor. An inactive cache has no effect on future operations. The snapshot therefore excludes `output`; it does not promise equivalence for arbitrarily injected internal states.
    pub fn context(&self) -> TranscriptContext<F64, [F64; 4]> {
        let mut pending = [None; 8];
        let input = &self.pending[..self.n_pending];
        let mut i = 0;
        while i < pending.len() && 8 * i < input.len() {
            let start = 8 * i;
            let end = (start + 8).min(input.len());
            let bytes = &input[start..end];
            let word = if bytes.len() == 8 {
                u64::from_le_bytes(bytes.try_into().unwrap())
            } else {
                let mut padded = [0u8; 8];
                padded[..bytes.len()].copy_from_slice(bytes);
                u64::from_le_bytes(padded)
            };
            pending[i] = Some(F64(word));
            i += 1;
        }
        TranscriptContext {
            state: words(self.cv),
            pending,
            pending_bytes: self.n_pending,
            first: self.first,
            previous: self.previous,
            squeezed: self.squeezed,
        }
    }

    /// Absorb an arbitrary byte string, preserving full blocks until their finality is known.
    pub fn absorb(&mut self, mut input: &[u8]) {
        if input.is_empty() {
            return;
        }
        if self.squeezed != 0 {
            self.previous = self.squeezed;
            self.squeezed = 0;
        }
        while !input.is_empty() {
            if self.n_pending == 64 {
                self.cv = compress_block(
                    self.cv,
                    &self.pending,
                    absorb_tweak(self.first, false, 64, self.previous),
                );
                self.first = false;
                self.previous = 0;
                self.n_pending = 0;
            }
            let take = input.len().min(64 - self.n_pending);
            self.pending[self.n_pending..self.n_pending + take].copy_from_slice(&input[..take]);
            self.n_pending += take;
            input = &input[take..];
        }
    }

    fn finalized(&self) -> [u32; 8] {
        if self.n_pending == 0 {
            return self.cv;
        }
        let mut block = self.pending;
        block[self.n_pending..].fill(0);
        compress_block(
            self.cv,
            &block,
            absorb_tweak(self.first, true, self.n_pending, self.previous),
        )
    }

    fn finish_absorb(&mut self) {
        if self.n_pending == 0 {
            return;
        }
        self.pending[self.n_pending..].fill(0);
        self.cv = compress_block(
            self.cv,
            &self.pending,
            absorb_tweak(self.first, true, self.n_pending, self.previous),
        );
        self.n_pending = 0;
        self.first = true;
        self.previous = 0;
    }

    /// Consume output bytes, retaining the unused suffix of each output block.
    ///
    /// # Panics
    ///
    /// A request exceeding [`MAX_SQUEEZE_BYTES`] in this run fails before modifying the state.
    pub fn squeeze(&mut self, mut output: &mut [u8]) {
        if output.is_empty() {
            return;
        }
        let len = u64::try_from(output.len()).expect("squeeze request exceeds cursor");
        assert!(
            len <= MAX_SQUEEZE_BYTES - self.squeezed,
            "squeeze request exceeds cursor"
        );
        self.finish_absorb();
        while !output.is_empty() {
            let offset = (self.squeezed % 32) as usize;
            if offset == 0 {
                let mut block = [0u8; 64];
                block[..8].copy_from_slice(&(self.squeezed / 32).to_le_bytes());
                let digest = compress_block(self.cv, &block, OUTPUT);
                let mut i = 0;
                while i < 8 {
                    self.output[4 * i..4 * i + 4].copy_from_slice(&digest[i].to_le_bytes());
                    i += 1;
                }
            }
            let take = output.len().min(32 - offset);
            output[..take].copy_from_slice(&self.output[offset..offset + take]);
            self.squeezed += take as u64;
            output = &mut output[take..];
        }
    }

    /// Absorb the scalar's three little-endian limbs, with no additional transport observation.
    pub fn observe(&mut self, x: F192) {
        let mut bytes = [0u8; 24];
        bytes[..8].copy_from_slice(&x.c0.to_le_bytes());
        bytes[8..16].copy_from_slice(&x.c1.to_le_bytes());
        bytes[16..24].copy_from_slice(&x.c2.to_le_bytes());
        self.absorb(&bytes);
    }

    /// Consume the next three little-endian limbs as an unbiased binary-field challenge.
    pub fn sample(&mut self) -> F192 {
        let mut bytes = [0u8; 24];
        self.squeeze(&mut bytes);
        let [a, b, c] = std::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()));
        F192::new(a, b, c)
    }

    /// Consume `n` scalar challenges in order.
    ///
    /// # Panics
    ///
    /// Refuses an exhausted output cursor before allocating or consuming any challenge.
    pub fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        let count = u64::try_from(n).expect("squeeze request exceeds cursor");
        assert!(
            count <= (MAX_SQUEEZE_BYTES - self.squeezed) / 24,
            "squeeze request exceeds cursor"
        );
        let mut samples = Vec::with_capacity(n);
        for _ in 0..n {
            samples.push(self.sample());
        }
        samples
    }

    /// Commit to the current history and cursor without changing either or revealing the CV.
    pub fn commitment(&self) -> [F64; 4] {
        let mut block = [0u8; 64];
        block[..8].copy_from_slice(&self.squeezed.to_le_bytes());
        words(compress_block(self.finalized(), &block, COMMIT))
    }

    fn pow_base(&self, bits: u32) -> [F64; 4] {
        let mut block = [0u8; 64];
        block[..8].copy_from_slice(&self.squeezed.to_le_bytes());
        block[8..16].copy_from_slice(&u64::from(bits).to_le_bytes());
        words(compress_block(self.finalized(), &block, POW_BASE))
    }

    fn absorb_nonce(&mut self, nonce: F192, bits: u32) {
        self.finish_absorb();
        let mut block = [0u8; 64];
        block[..8].copy_from_slice(&nonce.c0.to_le_bytes());
        block[8..16].copy_from_slice(&nonce.c1.to_le_bytes());
        block[16..24].copy_from_slice(&nonce.c2.to_le_bytes());
        block[24..32].copy_from_slice(&self.squeezed.to_le_bytes());
        block[32..40].copy_from_slice(&u64::from(bits).to_le_bytes());
        self.cv = compress_block(self.cv, &block, NONCE);
        self.squeezed = 0;
    }

    /// Find and bind the smallest `u64` nonce. Zero difficulty binds the canonical nonce zero.
    ///
    /// # Panics
    ///
    /// Difficulties above [`MAX_GRINDING_BITS`] and exhaustion of the nonce space are refused.
    pub fn grind_pow(&mut self, bits: u32) -> u64 {
        const PARALLEL_GRIND_MIN_HASHES: u64 = 1 << 13;
        assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
        self.finish_absorb();
        let nonce = if bits == 0 {
            0
        } else {
            let base = self.pow_base(bits);
            if (1u64 << bits) < PARALLEL_GRIND_MIN_HASHES {
                let mut n = 0u64;
                loop {
                    if pow_bits_ok(base, F192::new(n, 0, 0), bits) {
                        break n;
                    }
                    n = n.checked_add(1).expect("grinding exhausted nonce space");
                }
            } else {
                const BATCH: usize = 2 * primitives::hash::LANES;
                let mut template = [[0u8; 64]; BATCH];
                for input in &mut template {
                    for (slot, word) in input[..32].as_chunks_mut::<8>().0.iter_mut().zip(base) {
                        *slot = word.0.to_le_bytes();
                    }
                    input[56..].copy_from_slice(&POW_TAG.to_le_bytes());
                }
                // Keep the nonce as well as the batch index: do not hash the winning batch twice.
                let best = AtomicU64::new(u64::MAX);
                let batch = |first: u64| {
                    let mut inputs = template;
                    for (i, input) in inputs.iter_mut().enumerate() {
                        input[32..40].copy_from_slice(&(first + i as u64).to_le_bytes());
                    }
                    let mut digests = [[0u8; 32]; BATCH];
                    primitives::hash::hash_many::<64>(inputs.as_flattened(), digests.as_flattened_mut());
                    digests
                        .iter()
                        .position(|d| u64::from_le_bytes(d[..8].try_into().unwrap()) & ((1u64 << bits) - 1) == 0)
                        .is_some_and(|i| {
                            best.fetch_min(first + i as u64, Ordering::Relaxed);
                            true
                        })
                };
                let block = 1u64 << (bits.min(24) + 1);
                let mut start = 0u64;
                loop {
                    if parallel::find_first(block as usize / BATCH, |i| batch(start + (i * BATCH) as u64)).is_some() {
                        break best.load(Ordering::Relaxed);
                    }
                    start = start.checked_add(block).expect("grinding exhausted nonce space");
                }
            }
        };
        self.absorb_nonce(F192::new(nonce, 0, 0), bits);
        nonce
    }

    /// Check and bind a full-field nonce. A failed check must cause the caller to reject the proof.
    ///
    /// # Panics
    ///
    /// Difficulties above [`MAX_GRINDING_BITS`] are refused before changing the transcript.
    pub fn verify_pow_field(&mut self, nonce: F192, bits: u32) -> bool {
        assert!(bits <= MAX_GRINDING_BITS, "grinding past the digest's low word");
        self.finish_absorb();
        let ok = if bits == 0 {
            nonce == F192::ZERO
        } else {
            pow_bits_ok(self.pow_base(bits), nonce, bits)
        };
        self.absorb_nonce(nonce, bits);
        ok
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fresh() -> Duplex {
        Duplex::from_label(b"duplex-test")
    }

    fn decode_hex(text: &str) -> Vec<u8> {
        text.as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    #[test]
    fn independent_full_run_known_answers() {
        let domain = digest_words(&primitives::hash::hash(b"duplex-kat"));
        let statement = digest_words(&std::array::from_fn(|i| i as u8));
        let mut duplex = Duplex::new(domain, statement);
        duplex.absorb(&(0..131).collect::<Vec<u8>>());
        let mut first = [0u8; 97];
        duplex.squeeze(&mut first);
        assert_eq!(
            first.as_slice(),
            decode_hex(
                "eddf1764576c00950c9c492af01495de8b8e79efc1aab14061c0a6cd9e5d95166444228f37f0cf64f29b5ae1b7d1e852e80cadbd3fac6774bb2277975954becbf4d24ebb6faeb39d11332d425bd36b9549b1d522004ea004e6609fae6c32b0cf88"
            )
        );
        duplex.absorb(&[0, b'x'].repeat(33));
        let mut second = [0u8; 73];
        duplex.squeeze(&mut second);
        assert_eq!(
            second.as_slice(),
            decode_hex(
                "56ec3e8860bd2f6cc4ec3bd92213935e3218ff7acbd76f336b3f4635e7aa66f716d4a9a90e317a1944f24c05474f9cf09a9c3488bf181324c2deab88e59c1114b5d7c19c25f89a759c"
            )
        );
        let commitment: Vec<u8> = duplex
            .commitment()
            .into_iter()
            .flat_map(|word| word.0.to_le_bytes())
            .collect();
        assert_eq!(
            commitment,
            decode_hex("7a4c608370b4c73d53f4fb25e5dc647926cd422ed267ee11e04e02a6abefeaff")
        );
    }

    #[test]
    fn exporting_does_not_end_an_absorb_run_or_consume_output() {
        for size in [1, 63, 64, 65, 128] {
            let mut plain = fresh();
            plain.absorb(&vec![9; size]);
            let mut exported = plain.clone();
            exported.commitment();
            plain.absorb(b"continued");
            exported.absorb(b"continued");
            assert_eq!(plain.sample(), exported.sample());
            exported.commitment();
            assert_eq!(plain.sample_vec(5), exported.sample_vec(5));
        }
    }

    #[test]
    fn context_preserves_raw_absorption_and_partial_output_cursors() {
        for absorbed in [0, 1, 7, 8, 9, 63, 64, 65, 128, 129] {
            for consumed in [0, 1, 23, 24, 31, 32, 33, 95] {
                let mut plain = fresh();
                plain.absorb(&vec![7; absorbed]);
                plain.squeeze(&mut vec![0; consumed]);
                let mut captured = plain.clone();
                let _ = captured.context();
                assert_eq!(captured.sample_vec(5), plain.sample_vec(5));
                captured.absorb(b"continued");
                plain.absorb(b"continued");
                let _ = captured.context();
                assert_eq!(captured.sample_vec(5), plain.sample_vec(5));
            }
        }
    }

    #[test]
    fn chunking_and_empty_calls_preserve_long_streams() {
        let input: Vec<u8> = (0..4097).map(|i| i as u8).collect();
        let mut whole = fresh();
        whole.absorb(&input);
        let mut expected = [0u8; 1025];
        whole.squeeze(&mut expected);
        for chunk in [1, 23, 24, 31, 32, 63, 64, 65, 193] {
            let mut split = fresh();
            for part in input.chunks(chunk) {
                split.absorb(part);
                split.squeeze(&mut []);
            }
            let mut actual = [0u8; 1025];
            for part in actual.chunks_mut(chunk) {
                split.absorb(&[]);
                split.squeeze(part);
            }
            assert_eq!(actual, expected);
            assert_eq!(split.commitment(), whole.commitment());
            split.absorb(b"next");
            let mut reference = whole.clone();
            reference.absorb(b"next");
            assert_eq!(split.sample(), reference.sample());
        }
    }

    #[test]
    fn padding_cursor_domains_and_statement_are_bound() {
        let challenge = |data: &[u8], count: usize| {
            let mut state = fresh();
            state.squeeze(&mut vec![0; count]);
            state.absorb(data);
            state.sample()
        };
        assert_ne!(challenge(&[1], 0), challenge(&[1, 0], 0));
        assert_ne!(challenge(&[0; 63], 0), challenge(&[0; 64], 0));
        assert_ne!(challenge(&[0; 64], 0), challenge(&[0; 65], 0));
        assert_ne!(challenge(b"x", 1), challenge(b"x", 2));
        assert_ne!(challenge(b"x", 31), challenge(b"x", 32));
        let d = [F64(1); 4];
        let s = [F64(2); 4];
        assert_ne!(Duplex::new(d, s).sample(), Duplex::new(s, d).sample());
        assert_ne!(Duplex::new(d, s).sample(), Duplex::new(d, d).sample());
    }

    #[test]
    fn cloning_preserves_pending_input_and_unused_output() {
        for absorbed in [0, 1, 63, 64, 65, 127, 128, 129] {
            for consumed in [0, 1, 23, 24, 31, 32, 33, 95] {
                let mut original = fresh();
                original.absorb(&vec![7; absorbed]);
                original.squeeze(&mut vec![0; consumed]);
                let mut clone = original.clone();
                let before = original.commitment();
                assert_eq!(before, clone.commitment());
                assert_eq!(original.sample_vec(5), clone.sample_vec(5));
                original.absorb(b"left");
                clone.absorb(b"right");
                assert_ne!(original.sample(), clone.sample());
            }
        }
    }

    #[test]
    fn overflow_is_rejected_before_mutation() {
        let mut state = fresh();
        state.absorb(b"pending");
        state.squeezed = MAX_SQUEEZE_BYTES;
        let before = state.commitment();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| state.squeeze(&mut [0])));
        assert!(result.is_err());
        assert_eq!(state.commitment(), before);
        state.squeeze(&mut []);
        assert_eq!(state.commitment(), before);
    }

    #[test]
    fn grinding_is_minimal_and_binds_difficulty_and_full_nonce() {
        let mut initial = fresh();
        initial.observe(F192::new(7, 8, 9));
        initial.sample();
        initial.observe(F192::new(10, 11, 12));
        for bits in [0, 8, 13, 17] {
            let mut prover = initial.clone();
            let nonce = prover.grind_pow(bits);
            let base = initial.pow_base(bits);
            let expected = (0..=nonce)
                .find(|&n| pow_bits_ok(base, F192::new(n, 0, 0), bits))
                .unwrap();
            assert_eq!(nonce, expected);
            let mut verifier = initial.clone();
            assert!(verifier.verify_pow_field(F192::new(nonce, 0, 0), bits));
            assert_eq!(prover.sample_vec(5), verifier.sample_vec(5));
        }
        let bits = 8;
        let base = initial.pow_base(bits);
        let nonce = (0..u64::MAX)
            .map(|n| F192::new(n, 1, 2))
            .find(|&n| pow_bits_ok(base, n, bits))
            .unwrap();
        let mut verifier = initial.clone();
        assert!(verifier.verify_pow_field(nonce, bits));
        let mut expected = initial.clone();
        expected.absorb_nonce(nonce, bits);
        assert_eq!(verifier.sample(), expected.sample());
        let mut other_difficulty = initial.clone();
        other_difficulty.absorb_nonce(nonce, bits + 1);
        other_difficulty.sample();
        assert_ne!(expected.sample(), other_difficulty.sample());
        assert!(!initial.verify_pow_field(F192::new(0, 1, 0), 0));
    }

    #[test]
    #[should_panic(expected = "grinding past the digest's low word")]
    fn grinding_past_the_low_word_is_refused() {
        fresh().verify_pow_field(F192::new(1, 0, 0), 64);
    }
}
