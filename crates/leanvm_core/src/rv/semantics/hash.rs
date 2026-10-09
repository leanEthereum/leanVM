//! The BLAKE2s compression instruction, and its access to its block.

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, Products, WordGadgets};
use flock::circuit::{Builder, Circuit, Wire};
use primitives::hash::{G_LANES, IV, SIGMA};

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
        let half = |x: &[Wire; 64], i: usize| -> [Wire; 32] { std::array::from_fn(|j| x[32 * (i % 2) + j]) };
        let literal = |x: u32| -> [Wire; 32] { std::array::from_fn(|i| Wire::constant(x >> i & 1 == 1)) };
        let rotr = |w: &[Wire; 32], r: usize| -> [Wire; 32] { std::array::from_fn(|i| w[(i + r) % 32]) };

        // The inputs as 32-bit words: the counter, the finalization word, h and m.
        let t = c.input::<64>(0);
        let f0 = c.input::<32>(1);
        let h: Vec<[Wire; 32]> = (0..8).map(|i| half(&c.input(2 + i / 2), i)).collect();
        let m: Vec<[Wire; 32]> = (0..16).map(|i| half(&c.input(6 + i / 2), i)).collect();

        // The working vector: h, the IV, with the counter and the finalization word XORed in.
        let mut v = h.clone();
        v.extend(IV[..4].iter().map(|&x| literal(x)));
        for (i, x) in [half(&t, 0), half(&t, 1), f0, [Wire::ZERO; 32]].into_iter().enumerate() {
            let iv = literal(IV[4 + i]);
            v.push(c.xor_word(&iv, &x));
        }

        // Ten rounds of eight G's.
        for round in &SIGMA {
            for (g, &[a, b, cc, d]) in G_LANES.iter().enumerate() {
                for (x, r1, r2) in [(&m[round[2 * g]], 16, 12), (&m[round[2 * g + 1]], 8, 7)] {
                    let ab = c.add_wrapping(&v[a], &v[b]);
                    v[a] = c.add_wrapping(&ab, x);
                    let da = c.xor_word(&v[d], &v[a]);
                    v[d] = rotr(&da, r1);
                    v[cc] = c.add_wrapping(&v[cc], &v[d]);
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
        c.finish()
    }
}

/// The input ports in bits: `t`, `f0`, then the four words of `h` and the eight of `m`.
const INPUT_BITS: [usize; 14] = [64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64];

/// One instance of the circuit's witness, by word arithmetic instead of the gate walk.
///
/// It writes the same `z`, `A*z` and `B*z` the walk writes, into zeroed buffers.
///
/// The instance's bits, in order:
///
/// - words 0 to 13 are the inputs: `z` and `A*z` hold the word, `B*z` its wired bits;
/// - words 14 to 17 are the outputs: `z` and `A*z` hold the word, `B*z` all ones;
/// - bit 1152 is the constant, one in all three;
/// - from bit 1153, each 32-bit addition has a run of carry products, one after another.
///
/// An addition `x + y` has carries `c = (x + y) ^ x ^ y`. Its run covers bits `low..31`, the carry out of bit 31 being no product;
/// `low` is zero but where a literal operand's low zero bits leave no carry yet, round 0's first `c + d` of a column G, whose `c` is
/// still the IV.
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

    // The constant, right after the ports, then each addition's run of carries, in the order the circuit made them.
    let n_ports = INPUT_BITS.len() + 4;
    let mut rows = Products::new([&mut z[n_ports..], &mut az[n_ports..], &mut bz[n_ports..]], 0);
    rows.push(1, 1, 1);

    // Ten rounds of eight G's, the working vector updated as the circuit updates it.
    //
    // Unrolled, every run's place is a constant, so the rows are written with no branch.
    macro_rules! round {
        ($r:literal) => {
            round!(@g $r 0); round!(@g $r 1); round!(@g $r 2); round!(@g $r 3);
            round!(@g $r 4); round!(@g $r 5); round!(@g $r 6); round!(@g $r 7);
        };
        (@g $r:literal $g:literal) => {
            let low = if $r == 0 && $g < 4 { IV[$g].trailing_zeros() } else { 0 };
            g(&mut v, &mut rows, G_LANES[$g], [m[SIGMA[$r][2 * $g]], m[SIGMA[$r][2 * $g + 1]]], low);
        };
    }
    round!(0);
    round!(1);
    round!(2);
    round!(3);
    round!(4);
    round!(5);
    round!(6);
    round!(7);
    round!(8);
    round!(9);
    rows.finish();

    // Input ports: the word, masked to the port's width.
    for (i, &bits) in INPUT_BITS.iter().enumerate() {
        let wired = u64::MAX >> (64 - bits);
        (z[i], az[i], bz[i]) = (inputs[i] & wired, inputs[i] & wired, wired);
    }

    // Output ports: the new chaining value, every bit copied out.
    let n_in = INPUT_BITS.len();
    for i in 0..4 {
        let word = |j: usize| u64::from(h[j] ^ v[j] ^ v[j + 8]);
        let out = word(2 * i) | word(2 * i + 1) << 32;
        (z[n_in + i], az[n_in + i], bz[n_in + i]) = (out, out, u64::MAX);
    }
}

/// One G on the working vector: its two halves, each three additions, the first `c + d`'s run from bit `low`.
#[inline(always)]
fn g(v: &mut [u32; 16], rows: &mut Products<'_>, [a, b, c, d]: [usize; 4], [x0, x1]: [u32; 2], low: u32) {
    for (x, r1, r2, low) in [(x0, 16, 12, low), (x1, 8, 7, 0)] {
        let ab = add(rows, v[a], v[b], 0);
        v[a] = add(rows, ab, x, 0);
        v[d] = (v[d] ^ v[a]).rotate_right(r1);
        v[c] = add(rows, v[c], v[d], low);
        v[b] = (v[b] ^ v[c]).rotate_right(r2);
    }
}

/// `x + y`, its run of carry rows from bit `low`: `A*z = x ^ c = sum ^ y`, `B*z = y ^ c = sum ^ x`.
#[inline(always)]
fn add(rows: &mut Products<'_>, x: u32, y: u32, low: u32) -> u32 {
    let sum = x.wrapping_add(y);
    let mask = (1u64 << (31 - low)) - 1;
    rows.push(
        u64::from(sum ^ y) >> low & mask,
        u64::from(sum ^ x) >> low & mask,
        31 - low,
    );
    sum
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Class;
    use crate::rv::semantics::tests::{Ports, circuit_matches_reference, edge_word};
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
        let n_log = 8;
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
        // Chaining values and messages: all zero, all ones, every half's sign bit alone or clear, then random words.
        let rows: Vec<[u64; 14]> = (0..1 << n_log)
            .map(|i| {
                let t = [0, u32::MAX as u64, 1 << 32, u64::MAX]
                    .get(i)
                    .copied()
                    .unwrap_or_else(&mut next);
                let flags = [0, Hash::FINAL, next()][i % 3];
                let block = i % 8;
                std::array::from_fn(|k| match (k, block) {
                    (0, _) => t,
                    (1, _) => flags,
                    (_, 0) => 0,
                    (_, 1) => u64::MAX,
                    (_, 2) => 0x8000_0000_8000_0000,
                    (_, 3) => 0x7fff_ffff_7fff_ffff,
                    _ => next(),
                })
            })
            .collect();

        // Both generators on the same batch, every table compared.
        let walk = BLAKE2S.witness_by_walk(&rows, &[0; 14], n_log, |row, words| words.copy_from_slice(row));
        let fast =
            BLAKE2S.witness_by_instance(&rows, &[0; 14], n_log, |row, z, az, bz| blake2s_witness(row, z, az, bz));
        assert!(walk == fast, "the witness tables");
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
