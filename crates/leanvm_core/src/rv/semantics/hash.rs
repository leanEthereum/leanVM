//! The BLAKE2s compression instruction, and its access to its block.

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use flock::circuit::{Builder, Circuit, Wire};
use primitives::hash::{G_LANES, IV, SIGMA};
use std::sync::OnceLock;

/// One BLAKE2s compression instance, `blake2s rs1, rs2`: the finalization word, the counter, the block.
///
/// It compresses the 128-byte block at `rs1`, with the byte counter in `rs2`.
///
/// The block holds three parts:
///
/// - bytes 0 to 31: the chaining value;
/// - bytes 32 to 63: where the new chaining value goes;
/// - bytes 64 to 127: the message.
///
/// Word `k` of the block is the cell at `rs1 ^ 8k`.
///
/// That is `rs1 + 8k` when `rs1` is aligned to the block, as the guest library ensures.
///
/// An unaligned `rs1` permutes the words.
///
/// That is a guest bug, but a deterministic and provable one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hash {
    /// The finalization word: one of the legal words.
    pub flags: u64,
    /// The byte counter.
    pub t: u64,
    /// The block's words as found.
    pub block: [u64; Self::WORDS],
}

impl Hash {
    /// The chaining value's byte offset.
    pub const H: u64 = 0;
    /// The result's byte offset.
    pub const OUT: u64 = 32;
    /// The message's byte offset.
    pub const M: u64 = 64;
    /// The block's words.
    pub const WORDS: usize = 16;
    /// The block's bytes.
    pub const BLOCK_BYTES: u64 = 8 * Self::WORDS as u64;
    /// The finalization word of the last block: all ones.
    pub const FINAL: u64 = u32::MAX as u64;
}

impl InstructionClass for Hash {
    /// Not the last block, or the last.
    const LEGAL: &'static [u64] = &[0, Self::FINAL];

    /// The four words the instruction writes back: the new chaining value.
    type Output = [u64; 4];

    fn eval(&self) -> [u64; 4] {
        debug_assert!(Self::LEGAL.contains(&self.flags));

        // Split each 64-bit word into its two 32-bit halves, low first.
        let block = &self.block;
        let mut h: [u32; 8] = std::array::from_fn(|i| (block[i / 2] >> (32 * (i % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|i| (block[8 + i / 2] >> (32 * (i % 2))) as u32);

        // Compress, then pair the halves back into words.
        primitives::hash::compress(&mut h, &m, self.t, self.flags == Self::FINAL);
        std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
    }
}

/// A hash row's access to its block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockAccess {
    /// The block's words as the row found them.
    pub block: [u64; Hash::WORDS],
    /// The new chaining value, written to the block's result words.
    pub out: [u64; 4],
}

impl From<Hash> for BlockAccess {
    /// The access of a compression: its block, and the result it writes.
    fn from(hash: Hash) -> Self {
        Self {
            block: hash.block,
            out: hash.eval(),
        }
    }
}

impl ClassCircuit for Hash {
    /// The compression: `(t, f0, h, m) -> out`, on the 32-bit halves of the block's words.
    ///
    /// `h` and `out` are four words each, and `m` is eight.
    ///
    /// Each G is six 32-bit additions, its two three-operand ones chained.
    ///
    /// The state is never committed: only the carries are products, and the result is copied out.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&INPUT_BITS, &[64, 64, 64, 64]);
        let half = |c: &Builder, port: usize, i: usize| -> Word { c.input(port)[32 * (i % 2)..][..32].to_vec() };
        let literal = |c: &Builder, x: u32| -> Word { (0..32).map(|i| c.one().filter(|_| x >> i & 1 == 1)).collect() };
        let rotr = |w: &[Wire], r: usize| -> Word { (0..32).map(|i| w[(i + r) % 32]).collect() };

        // The inputs as 32-bit words: the counter, the finalization word, h and m.
        let (t, f0) = (c.input(0), c.input(1));
        let h: Vec<Word> = (0..8).map(|i| half(&c, 2 + i / 2, i)).collect();
        let m: Vec<Word> = (0..16).map(|i| half(&c, 6 + i / 2, i)).collect();

        // Each addition records where its products went.
        //
        // Its products are its top bits, from the first bit where both operands exist.
        // Once one product is made, the carry is a wire, so every later bit has one too.
        let mut carries = Vec::with_capacity(SIGMA.len() * 8 * 6);
        let mut add32 = |c: &mut Builder, x: &[Wire], y: &[Wire]| -> Word {
            let slot = c.next_slot();
            let sum = c.add_wrapping(x, y);
            let products = (c.next_slot() - slot) as u32;
            carries.push(Carries {
                slot: slot as u32,
                low: 31 - products,
            });
            sum
        };

        // The working vector: h, the IV, with the counter and the finalization word XORed in.
        let mut v = h.clone();
        v.extend(IV[..4].iter().map(|&x| literal(&c, x)));
        for (i, x) in [&t[..32], &t[32..], &f0, &[None; 32]].into_iter().enumerate() {
            let iv = literal(&c, IV[4 + i]);
            v.push(c.xor_word(&iv, x));
        }

        // Ten rounds of eight G's.
        for round in &SIGMA {
            for (g, &[a, b, cc, d]) in G_LANES.iter().enumerate() {
                for (x, r1, r2) in [(&m[round[2 * g]], 16, 12), (&m[round[2 * g + 1]], 8, 7)] {
                    let ab = add32(&mut c, &v[a], &v[b]);
                    v[a] = add32(&mut c, &ab, x);
                    let da = c.xor_word(&v[d], &v[a]);
                    v[d] = rotr(&da, r1);
                    v[cc] = add32(&mut c, &v[cc], &v[d]);
                    let bc = c.xor_word(&v[b], &v[cc]);
                    v[b] = rotr(&bc, r2);
                }
            }
        }

        // The new chaining value: h ^ v_low ^ v_high, half by half.
        for i in 0..8 {
            let hv = c.xor_word(&h[i], &v[i]);
            let out = c.xor_word(&hv, &v[i + 8]);
            for (bit, &wire) in out.iter().enumerate() {
                c.output(i / 2, 32 * (i % 2) + bit, wire);
            }
        }
        // Publish the carry runs for the word witness; every build records the same runs.
        let _ = CARRIES.set(carries);
        c.finish()
    }
}

/// The input ports in bits: `t`, `f0`, then the four words of `h` and the eight of `m`.
const INPUT_BITS: [usize; 14] = [64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64];

/// The hash circuit's carry runs, one per 32-bit addition, in the order the circuit makes them.
///
/// Building the circuit records them, and the word witness reads them.
static CARRIES: OnceLock<Vec<Carries>> = OnceLock::new();

/// Where one 32-bit addition put its carry products.
#[derive(Clone, Copy, Debug)]
struct Carries {
    /// The slot of the first product.
    slot: u32,
    /// The lowest bit with a product.
    ///
    /// The bits below are structural zeros: a literal operand's low zero bits, with no carry yet.
    low: u32,
}

/// One instance of the circuit's witness, by word arithmetic instead of the gate walk.
///
/// It writes the same `z`, `A*z` and `B*z` the walk writes, into zeroed buffers.
///
/// The instance's bits, in order:
///
/// - words 0 to 13 are the inputs: `z` and `A*z` hold the word, `B*z` its wired bits;
/// - words 14 to 17 are the outputs: `z` and `A*z` hold the word, `B*z` all ones;
/// - bit 1152 is the constant, one in all three;
/// - from bit 1153, each 32-bit addition has a run of carry products.
///
/// An addition `x + y` has carries `c = (x + y) ^ x ^ y`.
///
/// At bit `i` of its run:
///
/// ```text
///     A*z = x_i ^ c_i
///     B*z = y_i ^ c_i
///     z   = (x_i ^ c_i) * (y_i ^ c_i)
/// ```
pub fn blake2s_witness(inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
    assert_eq!(inputs.len(), INPUT_BITS.len());

    // The carry runs, recorded by building the circuit, once.
    let carries = CARRIES.get().unwrap_or_else(|| {
        Hash::circuit();
        CARRIES.get().expect("building the circuit records its carry runs")
    });

    // Input ports: the word, masked to the port's width.
    for (i, &bits) in INPUT_BITS.iter().enumerate() {
        let wired = u64::MAX >> (64 - bits);
        (z[i], az[i], bz[i]) = (inputs[i] & wired, inputs[i] & wired, wired);
    }

    // The working vector, as the circuit starts it.
    let half = |w: u64, i: usize| (w >> (32 * (i % 2))) as u32;
    let h: [u32; 8] = std::array::from_fn(|i| half(inputs[2 + i / 2], i));
    let m: [u32; 16] = std::array::from_fn(|i| half(inputs[6 + i / 2], i));
    let (t, f0) = (inputs[0], inputs[1] as u32);
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(&h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    v[14] ^= f0;

    // Each addition writes its run of carries, in the order the circuit made them.
    let mut runs = carries.iter();
    let mut add = |x: u32, y: u32| -> u32 {
        let Carries { slot, low } = *runs.next().expect("one run per addition");
        let sum = x.wrapping_add(y);
        let carry = sum ^ x ^ y;

        // The run covers bits low..31: the carry out of bit 31 is no product.
        let mask = (1u64 << (31 - low)) - 1;
        let left = u64::from(x ^ carry) >> low & mask;
        let right = u64::from(y ^ carry) >> low & mask;
        or_run(z, slot, left & right);
        or_run(az, slot, left);
        or_run(bz, slot, right);
        sum
    };

    // Ten rounds of eight G's, the working vector updated as the circuit updates it.
    for round in &SIGMA {
        for (g, &[a, b, c, d]) in G_LANES.iter().enumerate() {
            for (x, r1, r2) in [(m[round[2 * g]], 16, 12), (m[round[2 * g + 1]], 8, 7)] {
                let ab = add(v[a], v[b]);
                v[a] = add(ab, x);
                v[d] = (v[d] ^ v[a]).rotate_right(r1);
                v[c] = add(v[c], v[d]);
                v[b] = (v[b] ^ v[c]).rotate_right(r2);
            }
        }
    }

    // Output ports: the new chaining value, every bit copied out.
    let n_in = INPUT_BITS.len();
    for i in 0..4 {
        let word = |j: usize| u64::from(h[j] ^ v[j] ^ v[j + 8]);
        let out = word(2 * i) | word(2 * i + 1) << 32;
        (z[n_in + i], az[n_in + i], bz[n_in + i]) = (out, out, u64::MAX);
    }

    // The constant wire, right after the ports.
    let one = 64 * (n_in + 4);
    for buf in [z, az, bz] {
        buf[one / 64] |= 1 << (one % 64);
    }
}

/// OR a run of at most 32 bits into `buf`, from bit `slot`.
#[inline(always)]
const fn or_run(buf: &mut [u64], slot: u32, bits: u64) {
    let (word, shift) = (slot as usize / 64, slot % 64);
    buf[word] |= bits << shift;

    // The run's spill into the next word: (x >> 1) >> (63 - s) is x >> (64 - s), with no overflow at s = 0.
    buf[word + 1] |= (bits >> 1) >> (63 - shift);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{Ports, circuit_matches_reference, edge_word, run};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;
    use std::sync::LazyLock;

    /// Any compression instance with a legal finalization word.
    impl Arbitrary for Hash {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                proptest::array::uniform16(edge_word()),
            )
                .prop_map(|(flags, t, block)| Self { flags, t, block })
                .boxed()
        }
    }

    static BLAKE2S: LazyLock<Circuit> = LazyLock::new(Hash::circuit);

    #[test]
    fn hash_circuit_matches_the_reference() {
        // Legal flags and edge-biased operands pin the gate list to the reference function.
        circuit_matches_reference::<Hash>(64);
    }

    #[test]
    fn the_word_witness_is_the_gate_walk() {
        // Invariant: the word-level witness writes the tables the gate walk writes.
        //
        // The walk is the reference: it reads the circuit itself, slot by slot.
        let n_log = 5;
        let mut state = 0xA7u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        // Fixture: counters at the edges of their halves, then random ones.
        //
        // Finalization words: the legal two, and any word, whose high half the port drops.
        let rows: Vec<[u64; 14]> = (0..1 << n_log)
            .map(|i| {
                let t = [0, u32::MAX as u64, 1 << 32, u64::MAX]
                    .get(i)
                    .copied()
                    .unwrap_or_else(&mut next);
                let flags = [0, Hash::FINAL, next()][i % 3];
                std::array::from_fn(|k| match k {
                    0 => t,
                    1 => flags,
                    _ => next(),
                })
            })
            .collect();

        // Both generators on the same batch, every table compared.
        let walk = BLAKE2S.generate_witness(&rows, n_log);
        let fast =
            BLAKE2S.generate_witness_with(&rows, &[0; 14], n_log, |row, z, az, bz| blake2s_witness(row, z, az, bz));
        assert!(walk.0[..] == fast.0[..], "z");
        assert!(walk.1[..] == fast.1[..], "A*z");
        assert!(walk.2[..] == fast.2[..], "B*z");
        assert!(walk.3[..] == fast.3[..], "lincheck stripes");
    }

    proptest! {
        #[test]
        fn any_finalization_word_is_xored_in(hash in any::<Hash>(), f0 in any::<u32>()) {
            // Any 32-bit finalization word, against flock's compression, which takes one.
            let half = |w: &[u64]| -> Vec<u32> { w.iter().flat_map(|&w| [w as u32, (w >> 32) as u32]).collect() };
            let h = half(&hash.block[..4]).try_into().unwrap();
            let m = half(&hash.block[8..]).try_into().unwrap();
            let out = flock::hash::blake2s_compress(&h, &m, hash.t, f0, 0);
            let expected: Vec<u64> = (0..4).map(|i| out[2 * i] as u64 | (out[2 * i + 1] as u64) << 32).collect();
            let inputs = Hash { flags: f0 as u64, ..hash }.input_words();
            prop_assert_eq!(run(&BLAKE2S, &inputs, 4), expected);
        }
    }

    impl Ports for Hash {
        const CLASS: Class = Class::Hash;

        // The counter, the finalization word, the chaining value, then the message.
        fn input_words(&self) -> Vec<u64> {
            [self.t, self.flags]
                .into_iter()
                .chain(self.block[..4].iter().chain(&self.block[8..]).copied())
                .collect()
        }

        fn output_words(&self, out: &[u64; 4]) -> Vec<u64> {
            out.to_vec()
        }
    }
}
