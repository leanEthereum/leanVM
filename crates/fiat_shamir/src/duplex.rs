//! The duplex sponge: a byte string absorbed, a byte stream squeezed.
//!
//! The transcript layer runs over any duplex sponge.
//!
//! This one is built from the BLAKE2s compression function, the hash the VM proves.
//!
//! # The mode
//!
//! The state is a 32-byte chaining value `cv`.
//!
//! Each step is one BLAKE2s compression `F(cv, block, counter)`:
//!
//! - the seed compresses the IV, padded with zeros, into the first `cv`;
//! - an absorb compresses each 64-byte input block into a new `cv`;
//! - a squeeze compresses the output index into 32 output bytes, leaving `cv` unchanged.
//!
//! The counter frames each step: its role, and for an absorbed block its length and position.
//!
//! The role sits in the counter's top byte, which a plain BLAKE2s hash never sets.
//! So no transcript step is ever a compression of a plain hash or of a Merkle tree.
//!
//! # Streaming
//!
//! - Two absorbs in a row are one absorb of their concatenation.
//! - Two squeezes in a row are one squeeze of their total length.
//! - An absorb after a squeeze binds how many bytes were squeezed.
//!
//! The last input block is held back until the mode switches.
//! Its finality is only known then, so splitting the input never changes the state.
//!
//! # Security
//!
//! Modeling the compression as a random function, the mode is indifferentiable from a random oracle.
//!
//! The argument is Daemen-Mennink-Van Assche's tree-hashing theorem (`doc/leanvm` sec:e2e-fiat-shamir).
//!
//! The loss is `q^2 / 2^257` for `q` compressions.

use primitives::hash::{PARAM_IV, compress};

/// A duplex sponge over bytes.
///
/// Every implementation must stream: splitting a call into several never changes the bytes squeezed.
pub trait DuplexSponge: Clone {
    /// The sponge started from a 32-byte initialization vector, such as a session identifier.
    fn init(iv: [u8; 32]) -> Self;

    /// Absorb `input`.
    fn absorb(&mut self, input: &[u8]);

    /// Fill `output` with the next squeezed bytes.
    fn squeeze(&mut self, output: &mut [u8]);
}

/// The role of a node, in the top byte of its compression counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Role {
    /// The first node: the initialization vector.
    Seed = 1,
    /// A full block that opens an absorb run and does not close it.
    AbsorbFirst = 2,
    /// A full block in the middle of an absorb run.
    AbsorbMiddle = 3,
    /// The one block of a short absorb run, which opens and closes it.
    AbsorbOnly = 4,
    /// The block that closes an absorb run of several blocks.
    AbsorbLast = 5,
    /// One 32-byte output block, addressed by its index.
    Output = 6,
}

/// Bytes one squeeze run may consume: a 49-bit count fits the framing word.
pub const MAX_SQUEEZE: u64 = (1 << 49) - 1;

impl Role {
    /// The compression counter of a node of this role.
    ///
    /// ```text
    ///     bit  63 .. 56   55 .. 49   48 .. 0
    ///          role       length     previous
    /// ```
    ///
    /// - The length is the meaningful bytes of an absorbed block, 1 to 64.
    /// - Previous is the byte count of the squeeze run before, on an absorb run's first block.
    /// - Both are zero for the other roles.
    #[must_use]
    pub const fn counter(self, length: usize, previous: u64) -> u64 {
        ((self as u64) << 56) | ((length as u64) << 49) | previous
    }

    /// The role of an absorbed block, from whether it opens and whether it closes its run.
    #[must_use]
    pub const fn absorb(first: bool, last: bool) -> Self {
        match (first, last) {
            (true, false) => Self::AbsorbFirst,
            (false, false) => Self::AbsorbMiddle,
            (true, true) => Self::AbsorbOnly,
            (false, true) => Self::AbsorbLast,
        }
    }
}

/// The duplex sponge over the BLAKE2s compression function.
///
/// It holds at most one pending input block and one output block, and never allocates.
#[derive(Clone, Debug)]
pub struct Blake2sDuplex {
    /// The chaining value: everything absorbed so far.
    cv: [u32; 8],
    /// Input not yet compressed, at most one block.
    pending: [u8; 64],
    /// Bytes of `pending` in use.
    n_pending: usize,
    /// Whether the next compressed block opens an absorb run.
    first: bool,
    /// The byte count of the squeeze run the current absorb run follows.
    previous: u64,
    /// Bytes squeezed in the current squeeze run.
    squeezed: u64,
    /// The output block the next squeezed bytes come from.
    output: [u8; 32],
}

impl Blake2sDuplex {
    /// Compress the pending block into the chaining value.
    ///
    /// `last` says whether it closes its absorb run.
    fn compress_pending(&mut self, last: bool) {
        // Zero the unused tail: the framing word's length tells padding from data.
        self.pending[self.n_pending..].fill(0);
        let counter = Role::absorb(self.first, last).counter(self.n_pending, self.previous);
        self.cv = node(self.cv, &self.pending, counter);

        // The run continues past a full block, and only its first block carries the previous count.
        self.n_pending = 0;
        self.first = last;
        self.previous = 0;
    }
}

impl DuplexSponge for Blake2sDuplex {
    fn init(iv: [u8; 32]) -> Self {
        // The seed block is the initialization vector, then zeros.
        let mut block = [0; 64];
        block[..32].copy_from_slice(&iv);
        Self {
            cv: node(PARAM_IV, &block, Role::Seed.counter(0, 0)),
            pending: [0; 64],
            n_pending: 0,
            first: true,
            previous: 0,
            squeezed: 0,
            output: [0; 32],
        }
    }

    fn absorb(&mut self, mut input: &[u8]) {
        // An empty absorb is no absorb at all, and leaves a squeeze run open.
        if input.is_empty() {
            return;
        }

        // A squeeze run just ended: the next absorb run records its length.
        if self.squeezed != 0 {
            self.previous = self.squeezed;
            self.squeezed = 0;
        }

        while !input.is_empty() {
            // A full pending block is compressed only once more input shows it is not the last.
            if self.n_pending == 64 {
                self.compress_pending(false);
            }
            let take = input.len().min(64 - self.n_pending);
            self.pending[self.n_pending..self.n_pending + take].copy_from_slice(&input[..take]);
            self.n_pending += take;
            input = &input[take..];
        }
    }

    /// # Panics
    ///
    /// Panics when the squeeze run would pass `MAX_SQUEEZE` bytes, before changing the state.
    fn squeeze(&mut self, mut output: &mut [u8]) {
        // An empty squeeze is no squeeze at all, and leaves an absorb run open.
        if output.is_empty() {
            return;
        }
        let len = output.len() as u64;
        assert!(len <= MAX_SQUEEZE - self.squeezed, "squeeze run too long");

        // Close the absorb run: its pending block is its last.
        if self.n_pending != 0 {
            self.compress_pending(true);
        }

        while !output.is_empty() {
            // Output block `j` covers squeezed bytes `32j .. 32j + 32`.
            //
            // Its node reads the chaining value and leaves it unchanged.
            let offset = (self.squeezed % 32) as usize;
            if offset == 0 {
                let mut block = [0; 64];
                block[..8].copy_from_slice(&(self.squeezed / 32).to_le_bytes());
                self.output = state_bytes(node(self.cv, &block, Role::Output.counter(0, 0)));
            }

            // Hand out the unused part of the block, keeping the rest for the next squeeze.
            let take = output.len().min(32 - offset);
            output[..take].copy_from_slice(&self.output[offset..offset + take]);
            self.squeezed += take as u64;
            output = &mut output[take..];
        }
    }
}

/// One node: the final-flagged compression of `cv` and `block` at `counter`.
fn node(mut cv: [u32; 8], block: &[u8; 64], counter: u64) -> [u32; 8] {
    let (chunks, _) = block.as_chunks::<4>();
    let words = std::array::from_fn(|i| u32::from_le_bytes(chunks[i]));
    compress(&mut cv, &words, counter, true);
    cv
}

/// A chaining value as its 32 little-endian bytes.
fn state_bytes(cv: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (slot, word) in bytes.as_chunks_mut::<4>().0.iter_mut().zip(cv) {
        *slot = word.to_le_bytes();
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// One run of a transcript: bytes absorbed, or a count of bytes squeezed.
    #[derive(Clone, Debug)]
    enum Run {
        Absorb(Vec<u8>),
        Squeeze(usize),
    }

    // The mode written out node by node, with no buffering: what the streaming sponge must equal.
    //
    // Runs alternate, absorb runs non-empty, squeeze runs positive.
    fn reference(iv: [u8; 32], runs: &[Run]) -> Vec<u8> {
        let mut seed = [0; 64];
        seed[..32].copy_from_slice(&iv);
        let mut cv = node(PARAM_IV, &seed, Role::Seed.counter(0, 0));
        let mut previous = 0;
        let mut out = Vec::new();
        for run in runs {
            match run {
                Run::Absorb(bytes) => {
                    // Blocks of 64, the last one short and zero padded, the first one carrying the squeeze count.
                    let blocks: Vec<&[u8]> = bytes.chunks(64).collect();
                    for (i, chunk) in blocks.iter().enumerate() {
                        let mut block = [0; 64];
                        block[..chunk.len()].copy_from_slice(chunk);
                        let first = i == 0;
                        let role = Role::absorb(first, i + 1 == blocks.len());
                        cv = node(cv, &block, role.counter(chunk.len(), if first { previous } else { 0 }));
                    }
                }
                Run::Squeeze(n) => {
                    // Output blocks 0, 1, ... of the chaining value, cut to n bytes.
                    let mut stream = Vec::new();
                    for j in 0..n.div_ceil(32) as u64 {
                        let mut block = [0; 64];
                        block[..8].copy_from_slice(&j.to_le_bytes());
                        stream.extend(state_bytes(node(cv, &block, Role::Output.counter(0, 0))));
                    }
                    out.extend_from_slice(&stream[..*n]);
                    previous = *n as u64;
                }
            }
        }
        out
    }

    // Alternating runs: absorb runs of 1..200 bytes, squeeze runs of 1..100 bytes.
    fn runs() -> impl Strategy<Value = Vec<Run>> {
        let absorb = proptest::collection::vec(any::<u8>(), 1..200).prop_map(Run::Absorb);
        let squeeze = (1usize..100).prop_map(Run::Squeeze);
        proptest::collection::vec((absorb, squeeze), 1..5)
            .prop_map(|pairs| pairs.into_iter().flat_map(|(a, s)| [a, s]).collect())
    }

    proptest! {
        #[test]
        fn streaming_in_any_chunks_is_the_reference(runs in runs(), chunk in 1usize..70) {
            // Feed every run in pieces of `chunk` bytes, with empty calls between them.
            //
            // Splitting and empty calls must change nothing.
            let iv = [9; 32];
            let mut sponge = Blake2sDuplex::init(iv);
            let mut out = Vec::new();
            for run in &runs {
                match run {
                    Run::Absorb(bytes) => {
                        for piece in bytes.chunks(chunk) {
                            sponge.absorb(piece);
                            sponge.squeeze(&mut []);
                        }
                    }
                    Run::Squeeze(n) => {
                        let mut stream = vec![0; *n];
                        for piece in stream.chunks_mut(chunk) {
                            sponge.absorb(&[]);
                            sponge.squeeze(piece);
                        }
                        out.extend(stream);
                    }
                }
            }
            prop_assert_eq!(out, reference(iv, &runs));
        }
    }

    #[test]
    fn padding_and_squeeze_counts_are_bound() {
        // The framing tells apart transcripts a plain concatenation would merge.
        let challenge = |squeezed: usize, absorbed: &[u8]| {
            let mut sponge = Blake2sDuplex::init([0; 32]);
            sponge.absorb(b"x");
            sponge.squeeze(&mut vec![0; squeezed]);
            sponge.absorb(absorbed);
            let mut out = [0; 8];
            sponge.squeeze(&mut out);
            out
        };

        // A trailing zero byte is not padding:
        //
        //     [1] -> length 1,  [1, 0] -> length 2
        assert_ne!(challenge(1, &[1]), challenge(1, &[1, 0]));

        // A full last block is not a block followed by more input:
        //
        //     64 bytes -> one closing block,  65 bytes -> an opening block and a closing one
        assert_ne!(challenge(1, &[0; 64]), challenge(1, &[0; 65]));

        // The bytes squeezed before an absorb are part of its first block's framing:
        //
        //     31 squeezed vs 32 squeezed, the same output block either way
        assert_ne!(challenge(31, b"y"), challenge(32, b"y"));
    }

    #[test]
    fn a_squeeze_run_past_the_limit_is_refused_before_any_change() {
        // Fixture: a sponge whose run already consumed all but one byte of the limit.
        let mut sponge = Blake2sDuplex::init([0; 32]);
        sponge.squeeze(&mut [0; 1]);
        sponge.squeezed = MAX_SQUEEZE - 1;
        let before = sponge.clone();

        // Two more bytes cross the limit: the call panics, and the sponge is untouched.
        let crossed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| sponge.squeeze(&mut [0; 2])));
        assert!(crossed.is_err());
        assert_eq!(sponge.squeezed, before.squeezed);
        assert_eq!(sponge.cv, before.cv);
    }

    #[test]
    fn a_known_answer_pins_the_mode() {
        // Absorb 0..131, squeeze 40, absorb "ab", squeeze 8, from the iv 0..32.
        //
        // Any change to the framing, the padding or the byte order moves these bytes.
        let mut sponge = Blake2sDuplex::init(std::array::from_fn(|i| i as u8));
        sponge.absorb(&(0..131).collect::<Vec<u8>>());
        let mut first = [0; 40];
        sponge.squeeze(&mut first);
        sponge.absorb(b"ab");
        let mut second = [0; 8];
        sponge.squeeze(&mut second);
        let hex: String = first.iter().chain(&second).map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "72d518bf9786c4060f03f3cb68a3ffc32dda36374ed40d4bb910659749d061d422f71eefc6691565f8a51fa46683db43"
        );
    }
}
