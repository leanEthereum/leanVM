//! The BLAKE2s compression instruction, and its access to its block.

use super::InstructionClass;
use crate::rv::circuits::{ClassCircuit, Products, Word, WordGadgets};
use flock::circuit::{Builder, Circuit, Wire};
use primitives::hash::{G_LANES, IV, SIGMA};

/// One BLAKE2s compression instance, `blake2s rd, rs1, rs2, rs3`: three pointers and a word.
///
/// - the chaining value is the four words at `rs1`;
/// - the message is the eight words at `rs2`;
/// - the new chaining value goes to the four words at `rd`;
/// - `rs3` holds the byte counter.
///
/// Word `k` of each is the cell at its pointer `^ 8k`.
///
/// That is the pointer `+ 8k` for a chaining value on a 32-byte boundary and a message on a 64-byte one.
///
/// Elsewhere the words are permuted: a guest bug, but a deterministic and provable one.
///
/// The words are read before the result is written, so `rd` may be `rs1`.
///
/// A *node* is the hash of two digests whose order a bit chooses: the message's two halves are swapped when `rs3`'s
/// low bit is set, and the counter is 64, one block's.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Hash {
    /// The finalization word, then whether the instance is a node: one of the legal words.
    pub flags: u64,
    /// What `rs3` holds: the byte counter, or for a node the bit that orders the halves.
    pub x: u64,
    /// The chaining value's words as found.
    pub h: [u64; 4],
    /// The message's words as found.
    pub m: [u64; 8],
}

impl Hash {
    /// The finalization word of the last block: all ones.
    pub const FINAL: u64 = u32::MAX as u64;
    /// A node: the message's halves ordered by `rs3`'s low bit, the counter one block's.
    pub const NODE: u64 = 1 << 32;
    /// One block's bytes: a node's counter.
    pub const BLOCK_BYTES: u64 = 64;

    /// The message as compressed and its counter: a node's halves swapped by the bit, its counter one block's.
    pub const fn message(&self) -> ([u64; 8], u64) {
        if self.flags & Self::NODE == 0 {
            return (self.m, self.x);
        }
        let mut m = self.m;
        if self.x & 1 == 1 {
            m.rotate_left(4);
        }
        (m, Self::BLOCK_BYTES)
    }
}

impl InstructionClass for Hash {
    /// Not the last block, the last, or a node, which is one block.
    const LEGAL: &'static [u64] = &[0, Self::FINAL, Self::NODE | Self::FINAL];

    /// The four words the instruction writes: the new chaining value.
    type Output = [u64; 4];

    fn eval(&self) -> [u64; 4] {
        debug_assert!(Self::LEGAL.contains(&self.flags));

        // Split each 64-bit word into its two 32-bit halves, low first.
        let (message, t) = self.message();
        let mut h: [u32; 8] = std::array::from_fn(|i| (self.h[i / 2] >> (32 * (i % 2))) as u32);
        let m: [u32; 16] = std::array::from_fn(|i| (message[i / 2] >> (32 * (i % 2))) as u32);

        // Compress, then pair the halves back into words.
        primitives::hash::compress(&mut h, &m, t, self.flags & Self::FINAL == Self::FINAL);
        std::array::from_fn(|i| h[2 * i] as u64 | (h[2 * i + 1] as u64) << 32)
    }
}

/// A hash row's accesses: what its registers held and what its words held, before and after.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BlockAccess {
    /// The instance.
    pub hash: Hash,
    /// The address of the result: what `rd` holds.
    pub to: u64,
    /// The result's words as the row found them.
    pub old: [u64; 4],
    /// The new chaining value, written there.
    pub out: [u64; 4],
}

impl ClassCircuit for Hash {
    /// The compression: `(x, flags, h, m) -> out`, on the 32-bit halves of the words.
    ///
    /// `h` and `out` are four words each, and `m` is eight.
    ///
    /// A node's products come first: the bit that swaps the message's halves, the swap, then its counter.
    ///
    /// Each G is six 32-bit additions, its two three-operand ones chained.
    ///
    /// The state is never committed: only the carries are products, and the result is copied out.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&INPUT_BITS, &[64, 64, 64, 64]);
        let half = |c: &Builder, port: usize, i: usize| -> Word { c.input(port)[32 * (i % 2)..][..32].to_vec() };
        let literal = |c: &Builder, x: u32| -> Word { (0..32).map(|i| c.one().filter(|_| x >> i & 1 == 1)).collect() };
        let rotr = |w: &[Wire], r: usize| -> Word { (0..32).map(|i| w[(i + r) % 32]).collect() };

        // The inputs: the counter or the node's bit, the finalization word and the node selector, h and m.
        let (x, flags) = (c.input(0), c.input(1));
        let (f0, node) = (flags[..32].to_vec(), flags[32]);
        let h: Vec<Word> = (0..8).map(|i| half(&c, 2 + i / 2, i)).collect();

        // A node swaps the message's halves when its bit is set: each bit of a half moves by `swap * (low ^ high)`.
        let swap = c.and(node, x[0]);
        let mut words: Vec<Vec<Wire>> = (0..8).map(|k| c.input(6 + k)).collect();
        let (low, high) = words.split_at_mut(4);
        for (low, high) in low.iter_mut().zip(high) {
            for (l, h) in low.iter_mut().zip(high.iter_mut()) {
                let differ = c.xor(*l, *h);
                let moved = c.and(swap, differ);
                (*l, *h) = (c.xor(*l, moved), c.xor(*h, moved));
            }
        }
        let m: Vec<Word> = (0..16).map(|i| words[i / 2][32 * (i % 2)..][..32].to_vec()).collect();

        // A node's counter is one block's: each bit of the counter moves by `node * (x ^ 64)`.
        let t: Vec<Wire> = (0..64)
            .map(|bit| {
                let block = c.one().filter(|_| Self::BLOCK_BYTES >> bit & 1 == 1);
                let differ = c.xor(x[bit], block);
                let moved = c.and(node, differ);
                c.xor(x[bit], moved)
            })
            .collect();

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

/// The input ports in bits: `x`, the flags (`f0`, then the node selector), then the four words of `h` and the eight of `m`.
const INPUT_BITS: [usize; 14] = [64, 33, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64];

/// One instance of the circuit's witness, by word arithmetic instead of the gate walk.
///
/// It writes the same `z`, `A*z` and `B*z` the walk writes, into zeroed buffers.
///
/// The instance's bits, in order:
///
/// - words 0 to 13 are the inputs: `z` and `A*z` hold the word, `B*z` its wired bits;
/// - words 14 to 17 are the outputs: `z` and `A*z` hold the word, `B*z` all ones;
/// - bit 1152 is the constant, one in all three;
/// - from bit 1153, a node's products: the swap bit, the swap of the message's halves, and the counter's;
/// - then each 32-bit addition has a run of carry products, one after another.
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
    let (x, f0, node) = (inputs[0], inputs[1] as u32, inputs[1] >> 32 & 1);
    let swap = node & x & 1;
    let message: [u64; 8] = std::array::from_fn(|k| {
        let other = inputs[6 + (k + 4) % 8];
        inputs[6 + k] ^ (swap.wrapping_neg() & (inputs[6 + k] ^ other))
    });
    let m: [u32; 16] = std::array::from_fn(|i| half(message[i / 2], i));
    let t = x ^ (node.wrapping_neg() & (x ^ Hash::BLOCK_BYTES));
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

    // A node's products: the swap bit, each bit of the low half's words against the high half's, then the counter's.
    rows.push(node, x & 1, 1);
    for k in 0..4 {
        rows.push(swap.wrapping_neg(), inputs[6 + k] ^ inputs[10 + k], 64);
    }
    rows.push(node.wrapping_neg(), x ^ Hash::BLOCK_BYTES, 64);

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
                proptest::array::uniform4(edge_word()),
                proptest::array::uniform8(edge_word()),
            )
                .prop_map(|(flags, x, h, m)| Self { flags, x, h, m })
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
        // Flags: the legal three, and any word, whose bits past the node selector the port drops.
        // Chaining values and messages: all zero, all ones, every half's sign bit alone or clear, then random words.
        let rows: Vec<[u64; 14]> = (0..1 << n_log)
            .map(|i| {
                let t = [0, u32::MAX as u64, 1 << 32, u64::MAX]
                    .get(i)
                    .copied()
                    .unwrap_or_else(&mut next);
                let flags = [0, Hash::FINAL, Hash::NODE | Hash::FINAL, next()][i % 4];
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
        let walk = BLAKE2S.generate_witness(&rows, n_log);
        let fast =
            BLAKE2S.generate_witness_with(&rows, &[0; 14], n_log, |row, z, az, bz| blake2s_witness(row, z, az, bz));
        assert!(walk == fast, "the witness tables");
    }

    impl Ports for Hash {
        const CLASS: Class = Class::Hash;

        // The counter or the node's bit, the flags, the chaining value, then the message.
        fn input_words(&self) -> Vec<u64> {
            [self.x, self.flags]
                .into_iter()
                .chain(self.h.iter().chain(&self.m).copied())
                .collect()
        }

        fn output_words(&self, out: &[u64; 4]) -> Vec<u64> {
            out.to_vec()
        }
    }
}
