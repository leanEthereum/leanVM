//! Each instruction class's function ([`super::semantics`]) as a flock gate list.
//!
//! A circuit's ports are whole 64-bit words, and they are the words its table puts
//! on the bus: the values read from the registers, the bytecode's immediate and
//! flags, the result. A circuit is defined on its class's legal flags only, which
//! are one-hot where they select, so a selection is an XOR of products.

use flock::circuit::{Builder, Circuit, Wire};

/// A word of wires, low bit first.
type Word = Vec<Wire>;

fn xor_words(c: &mut Builder, x: &[Wire], y: &[Wire]) -> Word {
    x.iter().zip(y).map(|(&x, &y)| c.xor(x, y)).collect()
}

/// `s·x`, bit by bit.
fn gate_word(c: &mut Builder, s: Wire, x: &[Wire]) -> Word {
    x.iter().map(|&x| c.and(s, x)).collect()
}

/// Whether any bit of `x` is set.
fn any(c: &mut Builder, x: &[Wire]) -> Wire {
    x.iter().fold(None, |acc, &bit| c.or(acc, bit))
}

/// `x + y + carry_in`, and the carry out of the top bit.
fn add_with_carry(c: &mut Builder, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire) {
    let mut carry = carry_in;
    let mut sum = Vec::with_capacity(x.len());
    for (&x, &y) in x.iter().zip(y) {
        let xc = c.xor(x, carry);
        let yc = c.xor(y, carry);
        sum.push(c.xor(xc, y));
        let maj = c.and(xc, yc);
        carry = c.xor(maj, carry);
    }
    (sum, carry)
}

/// `x`, its bits from 32 up replaced by bit 31 when `word` is set.
fn sext32_if(c: &mut Builder, word: Wire, x: &[Wire]) -> Word {
    (0..64)
        .map(|i| if i < 32 { x[i] } else { c.mux(word, x[31], x[i]) })
        .collect()
}

/// `x + y` over `x.len()` bits, the carry out of the top bit dropped: one product
/// per bit but the top, the carry into bit `i + 1` being `maj(x_i, y_i, c_i)`.
fn add(c: &mut Builder, x: &[Wire], y: &[Wire]) -> Word {
    let (mut carry, width) = (None, x.len());
    let mut sum = Vec::with_capacity(width);
    for (i, (&x, &y)) in x.iter().zip(y).enumerate() {
        let xc = c.xor(x, carry);
        let yc = c.xor(y, carry);
        sum.push(c.xor(xc, y));
        // The carry out of the top bit falls off the modulus, so it is never a product.
        if i + 1 < width {
            let maj = c.and(xc, yc);
            carry = c.xor(maj, carry);
        }
    }
    sum
}

/// `x` shifted by `8·amount` bits, `amount` being three bits: left, or right.
fn shift_bytes(c: &mut Builder, x: &[Wire], amount: &[Wire], left: bool) -> Word {
    let mut x = x.to_vec();
    for (stage, &bit) in amount.iter().enumerate() {
        let by = 8 << stage;
        let from = |x: &[Wire], i: usize| {
            if left {
                i.checked_sub(by).and_then(|j| x[j])
            } else {
                x.get(i + by).copied().flatten()
            }
        };
        x = (0..64).map(|i| c.mux(bit, from(&x, i), x[i])).collect();
    }
    x
}

/// The width thresholds of a load or a store, from the two bits of `log2` of its
/// width in bytes: at least 2, at least 4, exactly 8.
fn width_thresholds(c: &mut Builder, log_width: &[Wire]) -> [Wire; 3] {
    [
        c.or(log_width[0], log_width[1]),
        log_width[1],
        c.and(log_width[0], log_width[1]),
    ]
}

/// [`super::semantics::bus_address`]: the low three bits are the ones misaligning the access.
fn bus_address(c: &mut Builder, address: &[Wire], thresholds: [Wire; 3]) -> Word {
    (0..64)
        .map(|i| {
            if i < 3 {
                c.and(address[i], thresholds[i])
            } else {
                address[i]
            }
        })
        .collect()
}

/// [`super::Class::Load`]'s circuit: `(v1, imm, flags, cell) -> (address, out)`, the
/// address being what goes on the memory bus and `cell` the word read there.
pub fn load() -> Circuit {
    let mut c = Builder::new(&[64, 64, 3, 64], &[64, 64]);
    let (v1, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let address = add(&mut c, &v1, &imm);
    let [ge2, ge4, eq8] = width_thresholds(&mut c, &flags[..2]);
    let bus = bus_address(&mut c, &address, [ge2, ge4, eq8]);
    let value = shift_bytes(&mut c, &cell, &address[..3], false);
    // The extension: the value's top bit, which the width places, if the load is signed.
    let (w1, w2, w4) = (c.not(ge2), c.xor(ge2, ge4), c.xor(ge4, eq8));
    let sign = [(w1, 7), (w2, 15), (w4, 31)]
        .into_iter()
        .fold(None, |acc, (width, bit)| {
            let term = c.and(width, value[bit]);
            c.xor(acc, term)
        });
    let extension = c.and(flags[2], sign);
    for (i, &wire) in bus.iter().enumerate() {
        c.output(0, i, wire);
    }
    for i in 0..64 {
        let keeps = match i {
            0..8 => None,
            8..16 => Some(ge2),
            16..32 => Some(ge4),
            _ => Some(eq8),
        };
        let wire = keeps.map_or(value[i], |keeps| c.mux(keeps, value[i], extension));
        c.output(1, i, wire);
    }
    c.finish()
}

/// [`super::Class::Store`]'s circuit: `(v1, v2, imm, flags, cell) -> (address, new cell,
/// out)`. `out` is what the row writes to its destination, the sink: zero.
pub fn store() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 2, 64], &[64, 64, 64]);
    let (v1, v2, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
    let address = add(&mut c, &v1, &imm);
    let [ge2, ge4, eq8] = width_thresholds(&mut c, &flags);
    let bus = bus_address(&mut c, &address, [ge2, ge4, eq8]);
    let value = shift_bytes(&mut c, &v2, &address[..3], true);
    // Byte `j` is written when it shares the access's block: bit `k` of `j` equals bit
    // `k` of the address wherever the width does not already span both.
    let spans: [[Wire; 2]; 3] = std::array::from_fn(|k| {
        let (is_zero, threshold) = (c.not(address[k]), [ge2, ge4, eq8][k]);
        [c.or(is_zero, threshold), c.or(address[k], threshold)]
    });
    for (i, &wire) in bus.iter().enumerate() {
        c.output(0, i, wire);
    }
    for j in 0..8 {
        let low = c.and(spans[0][j & 1], spans[1][(j >> 1) & 1]);
        let written = c.and(low, spans[2][j >> 2]);
        for i in 8 * j..8 * j + 8 {
            let wire = c.mux(written, value[i], cell[i]);
            c.output(1, i, wire);
        }
    }
    c.finish()
}

/// [`super::semantics::shift`]: `(v1, v2, imm, flags) -> out`. One right shifter serves
/// both directions, a left shift being a right shift of the reversed word.
pub fn shift() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
    let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let flag = |bit: u64| f[bit.trailing_zeros() as usize];
    use super::shift::*;
    let (right, arith, word) = (flag(RIGHT), flag(ARITH), flag(WORD));

    // The amount: six bits, five for a word shift.
    let mut amount: Word = (0..6).map(|i| c.xor(v2[i], imm[i])).collect();
    let not_word = c.not(word);
    amount[5] = c.and(not_word, amount[5]);
    // A word shift takes the low 32 bits, extended as the shift is: by the sign for an
    // arithmetic one, by zero otherwise.
    let low_sign = c.and(arith, v1[31]);
    let x: Word = (0..64)
        .map(|i| if i < 32 { v1[i] } else { c.mux(word, low_sign, v1[i]) })
        .collect();
    // What a right shift brings in from the top. `ARITH` comes with `RIGHT`.
    let fill = c.and(arith, x[63]);

    let reversed = |c: &mut Builder, x: &[Wire]| -> Word { (0..64).map(|i| c.mux(right, x[i], x[63 - i])).collect() };
    let mut y = reversed(&mut c, &x);
    for (stage, &bit) in amount.iter().enumerate() {
        let by = 1 << stage;
        y = (0..64)
            .map(|i| c.mux(bit, if i + by < 64 { y[i + by] } else { fill }, y[i]))
            .collect();
    }
    let y = reversed(&mut c, &y);
    for (i, &wire) in sext32_if(&mut c, word, &y).iter().enumerate() {
        c.output(0, i, wire);
    }
    c.finish()
}

/// [`super::semantics::mul`]: `(v1, v2, flags) -> out`, the low word of the product.
pub fn mul() -> Circuit {
    let mut c = Builder::new(&[64, 64, 1], &[64]);
    let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &v1, &v2, 64);
    for (i, &wire) in sext32_if(&mut c, f[0], &product).iter().enumerate() {
        c.output(0, i, wire);
    }
    c.finish()
}

/// [`super::semantics::mulh`]: `(v1, v2, flags) -> out`, the high word of the product.
/// The unsigned product's high word, less `v2` if `v1` is signed and negative, less `v1`
/// if `v2` is: a negative operand is its unsigned reading minus `2^64`.
pub fn mulh() -> Circuit {
    let mut c = Builder::new(&[64, 64, 2], &[64]);
    let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &v1, &v2, 128);
    let mut high = product[64..].to_vec();
    for (signed, operand, other) in [(f[0], &v1, &v2), (f[1], &v2, &v1)] {
        let negative = c.and(signed, operand[63]);
        // `high - other` is `high + !other + 1`.
        let subtrahend: Word = other
            .iter()
            .map(|&bit| {
                let inverted = c.not(bit);
                c.and(negative, inverted)
            })
            .collect();
        (high, _) = add_with_carry(&mut c, &high, &subtrahend, negative);
    }
    for (i, &wire) in high.iter().enumerate() {
        c.output(0, i, wire);
    }
    c.finish()
}

/// `x` negated if `negative`: `(x ^ negative) + negative`.
fn negate_if(c: &mut Builder, negative: Wire, x: &[Wire]) -> Word {
    let flipped: Word = x.iter().map(|&bit| c.xor(bit, negative)).collect();
    add_with_carry(c, &flipped, &[None; 64], negative).0
}

/// [`super::semantics::div`]: `(v1, v2, flags, q, r) -> (out, bad)`. The quotient's and
/// the remainder's magnitudes `q` and `r` are the prover's ([`super::semantics::div_hints`]),
/// and `bad` is set unless they are the ones: `|n| = q·|d| + r` over the integers (the
/// product's high word zero, the sum without a carry) and `r < |d|`. A row puts `bad`
/// where its bytecode entry holds zero, so it is zero. Dividing by zero checks nothing
/// and returns what the specification says, all ones or the dividend, and the one
/// overflow, `-2^63 / -1`, is no special case on magnitudes.
pub fn div() -> Circuit {
    let mut c = Builder::new(&[64, 64, 3, 64, 64], &[64, 1]);
    let (v1, v2, f, q, r) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
    let (signed, rem, word) = (f[0], f[1], f[2]);
    // A word form divides the low 32 bits, extended as the division is signed or not.
    let mut extend = |x: &[Wire]| -> Word {
        let sign = c.and(signed, x[31]);
        (0..64)
            .map(|i| if i < 32 { x[i] } else { c.mux(word, sign, x[i]) })
            .collect()
    };
    let (n, d) = (extend(&v1), extend(&v2));
    let (n_negative, d_negative) = (c.and(signed, n[63]), c.and(signed, d[63]));
    let (n_abs, d_abs) = (negate_if(&mut c, n_negative, &n), negate_if(&mut c, d_negative, &d));

    let (product, _) = flock::arith::mul::Multiplier::build(&mut c, &q, &d_abs, 128);
    let overflows = any(&mut c, &product[64..]);
    let (sum, carries) = add_with_carry(&mut c, &product[..64], &r, None);
    let difference = xor_words(&mut c, &sum, &n_abs);
    let differs = any(&mut c, &difference);
    // `r - |d|` does not borrow, which is `r + !|d| + 1` carrying out, when `r >= |d|`.
    let d_inverted: Word = d_abs.iter().map(|&bit| c.not(bit)).collect();
    let one = c.one();
    let (_, too_large) = add_with_carry(&mut c, &r, &d_inverted, one);
    let d_nonzero = any(&mut c, &d);
    let wrong = [carries, differs, too_large]
        .into_iter()
        .fold(overflows, |acc, w| c.or(acc, w));
    let bad = c.and(d_nonzero, wrong);

    // The quotient is negative when the operands' signs differ, the remainder when
    // the dividend is.
    let q_negative = c.xor(n_negative, d_negative);
    let (q_signed, r_signed) = (negate_if(&mut c, q_negative, &q), negate_if(&mut c, n_negative, &r));
    let out: Word = (0..64)
        .map(|i| {
            let result = c.mux(rem, r_signed[i], q_signed[i]);
            let by_zero = c.mux(rem, n[i], one);
            c.mux(d_nonzero, result, by_zero)
        })
        .collect();
    for (i, &wire) in sext32_if(&mut c, word, &out).iter().enumerate() {
        c.output(0, i, wire);
    }
    c.output(1, 0, bad);
    c.finish()
}

/// [`super::Class::Alu`]'s ports.
pub mod alu_ports {
    /// Input words: the two register values, the immediate, the flags.
    pub const V1: usize = 0;
    pub const V2: usize = 1;
    pub const IMM: usize = 2;
    pub const FLAGS: usize = 3;
    /// Output words.
    pub const OUT: usize = 4;
    pub const TAKEN: usize = 5;
}

/// [`super::semantics::alu`].
pub fn alu() -> Circuit {
    let mut c = Builder::new(&[64, 64, 64, 15], &[64, 1]);
    let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let flag = |bit: u64| f[bit.trailing_zeros() as usize];
    use super::alu::*;

    let b = xor_words(&mut c, &v2, &imm);
    // `v1 - b` is `v1 + !b + 1`, and it borrows exactly when that does not carry out.
    let sub = flag(SUB);
    let b_or_not: Word = b.iter().map(|&bit| c.xor(bit, sub)).collect();
    let (sum, carry_out) = add_with_carry(&mut c, &v1, &b_or_not, sub);
    let ltu = c.not(carry_out);
    let signs = c.xor(v1[63], b[63]);
    let lt = c.xor(ltu, signs);
    let diff = xor_words(&mut c, &v1, &b);
    let ne = any(&mut c, &diff);
    let eq = c.not(ne);

    // `out`: the sum unless a selector is set. AND is a product, OR is AND plus XOR.
    let sum = sext32_if(&mut c, flag(WORD), &sum);
    let selectors = [SEL_LT, SEL_LTU, SEL_AND, SEL_OR, SEL_XOR];
    let none = selectors.iter().fold(c.one(), |acc, &s| c.xor(acc, flag(s)));
    let and_or = c.xor(flag(SEL_AND), flag(SEL_OR));
    let or_xor = c.xor(flag(SEL_OR), flag(SEL_XOR));
    let mut out = gate_word(&mut c, none, &sum);
    for i in 0..64 {
        let both = c.and(v1[i], b[i]);
        let and_term = c.and(and_or, both);
        let xor_term = c.and(or_xor, diff[i]);
        let logic = c.xor(and_term, xor_term);
        out[i] = c.xor(out[i], logic);
    }
    let lt_term = c.and(flag(SEL_LT), lt);
    let ltu_term = c.and(flag(SEL_LTU), ltu);
    let compared = c.xor(lt_term, ltu_term);
    out[0] = c.xor(out[0], compared);
    let keep_bit0 = c.not(flag(CLEAR_BIT0));
    out[0] = c.and(keep_bit0, out[0]);

    let (ge, geu) = (c.not(lt), c.not(ltu));
    let taken = [
        (BR_EQ, eq),
        (BR_NE, ne),
        (BR_LT, lt),
        (BR_GE, ge),
        (BR_LTU, ltu),
        (BR_GEU, geu),
    ]
    .into_iter()
    .fold(flag(ALWAYS), |acc, (when, holds)| {
        let term = c.and(flag(when), holds);
        c.xor(acc, term)
    });

    for (i, &wire) in out.iter().enumerate() {
        c.output(0, i, wire);
    }
    c.output(1, 0, taken);
    c.finish()
}

/// [`super::Class::Hash`]'s circuit: `(t, f0, h, m) -> out`, the BLAKE2s compression
/// ([`super::semantics::blake2s`]) on the 32-bit halves of the block's words, `h`
/// and `out` four words each and `m` eight. Every G is six 32-bit additions, its
/// two three-operand ones chained, and the state is never materialized: only the
/// carries are products, and the result's words are copied out.
pub fn blake2s() -> Circuit {
    use primitives::hash::{G_LANES, IV, SIGMA};
    let mut c = Builder::new(
        &[64, 32, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64],
        &[64, 64, 64, 64],
    );
    let half = |c: &Builder, port: usize, i: usize| -> Word { c.input(port)[32 * (i % 2)..32 * (i % 2) + 32].to_vec() };
    let (t, f0) = (c.input(0), c.input(1));
    let h: Vec<Word> = (0..8).map(|i| half(&c, 2 + i / 2, i)).collect();
    let m: Vec<Word> = (0..16).map(|i| half(&c, 6 + i / 2, i)).collect();
    let literal = |c: &Builder, x: u32| -> Word { (0..32).map(|i| c.one().filter(|_| x >> i & 1 == 1)).collect() };
    let rotr = |w: &[Wire], r: usize| -> Word { (0..32).map(|i| w[(i + r) % 32]).collect() };

    let mut v = h.clone();
    v.extend(IV[..4].iter().map(|&x| literal(&c, x)));
    for (i, x) in [&t[..32], &t[32..], &f0, &[None; 32]].into_iter().enumerate() {
        let iv = literal(&c, IV[4 + i]);
        v.push(xor_words(&mut c, &iv, x));
    }
    for round in &SIGMA {
        for (g, &[a, b, cc, d]) in G_LANES.iter().enumerate() {
            for (x, r1, r2) in [(&m[round[2 * g]], 16, 12), (&m[round[2 * g + 1]], 8, 7)] {
                let ab = add(&mut c, &v[a], &v[b]);
                v[a] = add(&mut c, &ab, x);
                let da = xor_words(&mut c, &v[d], &v[a]);
                v[d] = rotr(&da, r1);
                v[cc] = add(&mut c, &v[cc], &v[d]);
                let bc = xor_words(&mut c, &v[b], &v[cc]);
                v[b] = rotr(&bc, r2);
            }
        }
    }
    for i in 0..8 {
        let hv = xor_words(&mut c, &h[i], &v[i]);
        let out = xor_words(&mut c, &hv, &v[i + 8]);
        for (bit, &wire) in out.iter().enumerate() {
            c.output(i / 2, 32 * (i % 2) + bit, wire);
        }
    }
    c.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics;
    use crate::transcript::{ProverState, VerifierState};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn word(&mut self) -> u64 {
            match self.next() % 6 {
                0 => [
                    0,
                    1,
                    u64::MAX,
                    1 << 63,
                    (1 << 63) - 1,
                    1 << 31,
                    0xffff_ffff,
                    (1 << 31) - 1,
                ][(self.next() % 8) as usize],
                1 => self.next() as i32 as i64 as u64,
                _ => self.next(),
            }
        }
    }

    /// The circuit's output words on `inputs`, read off the witness it generates.
    fn run(circuit: &Circuit, inputs: &[u64], outputs: std::ops::Range<usize>) -> Vec<u64> {
        let words = 1 << (circuit.k_log() - 6);
        let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);
        circuit.witness_instance(inputs, &mut z, &mut az, &mut bz);
        z[outputs].to_vec()
    }

    #[test]
    fn alu_is_its_reference() {
        let circuit = alu();
        assert_eq!(circuit.k_log(), 10, "an ALU instance is 16 packed words");
        let mut rng = Rng(0xA1);
        for &flags in &crate::rv::alu::LEGAL {
            for round in 0..400 {
                let v1 = rng.word();
                // Equal operands now and then, which random words never are.
                let v2 = if round % 7 == 0 { v1 } else { rng.word() };
                // One of `v2` and `imm` is zero, as the decoder has it.
                let (v2, imm) = if round % 2 == 0 { (v2, 0) } else { (0, v2) };
                let (out, taken) = semantics::alu(v1, v2, imm, flags);
                assert_eq!(
                    run(&circuit, &[v1, v2, imm, flags], alu_ports::OUT..alu_ports::TAKEN + 1),
                    [out, taken as u64],
                    "flags {flags:#x} on {v1:#x}, {v2:#x}, {imm:#x}"
                );
            }
        }
    }

    #[test]
    fn load_and_store_are_their_references() {
        let (load, store) = (load(), store());
        assert_eq!(
            (load.k_log(), store.k_log()),
            (10, 10),
            "an instance is 16 packed words"
        );
        let mut rng = Rng(0xA3);
        for round in 0..4000 {
            let (v1, imm, v2, cell) = (rng.word(), rng.next() % 4096, rng.word(), rng.next());
            let address = semantics::address(v1, imm);
            for &flags in &crate::rv::load::LEGAL {
                let log_width = flags & crate::rv::load::LOG_WIDTH;
                // Aligned every other round, which a random address seldom is.
                let v1 = if round % 2 == 0 {
                    v1 & !((1 << log_width) - 1)
                } else {
                    v1
                };
                let imm = if round % 2 == 0 { imm & !7 } else { imm };
                let address = if round % 2 == 0 {
                    semantics::address(v1, imm)
                } else {
                    address
                };
                assert_eq!(
                    run(&load, &[v1, imm, flags, cell], 4..6),
                    [
                        semantics::bus_address(address, log_width),
                        semantics::load(cell, address, flags)
                    ],
                    "load {flags:#x} at {address:#x} of {cell:#x}"
                );
            }
            for &flags in &crate::rv::store::LEGAL {
                let got = run(&store, &[v1, v2, imm, flags, cell], 5..8);
                assert_eq!(
                    got[0],
                    semantics::bus_address(address, flags),
                    "store {flags:#x} at {address:#x}"
                );
                assert_eq!(got[2], 0);
                // A misaligned store names no cell, so what it would write is nobody's business.
                if semantics::is_aligned(address, flags) {
                    assert_eq!(
                        got[1],
                        semantics::store(cell, address, v2, flags),
                        "store {flags:#x} at {address:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn shift_and_multiplications_are_their_references() {
        let (shift, mul, mulh) = (shift(), mul(), mulh());
        assert_eq!((shift.k_log(), mul.k_log(), mulh.k_log()), (10, 12, 13));
        let mut rng = Rng(0xA4);
        for round in 0..1500 {
            let (v1, v2) = (rng.word(), rng.word());
            for &flags in &crate::rv::shift::LEGAL {
                // Every amount now and then, which a random word's low bits cover slowly.
                let amount = if round % 3 == 0 { round as u64 % 64 } else { v2 };
                let (v2, imm) = if round % 2 == 0 { (amount, 0) } else { (0, amount & 63) };
                assert_eq!(
                    run(&shift, &[v1, v2, imm, flags], 4..5),
                    [semantics::shift(v1, v2, imm, flags)],
                    "shift {flags:#x} of {v1:#x} by {v2:#x}, {imm:#x}"
                );
            }
            if round % 10 == 0 {
                for &flags in &crate::rv::mul::LEGAL {
                    assert_eq!(
                        run(&mul, &[v1, v2, flags], 3..4),
                        [semantics::mul(v1, v2, flags)],
                        "mul {flags:#x}"
                    );
                }
                for &flags in &crate::rv::mulh::LEGAL {
                    assert_eq!(
                        run(&mulh, &[v1, v2, flags], 3..4),
                        [semantics::mulh(v1, v2, flags)],
                        "mulh {flags:#x} of {v1:#x}, {v2:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn div_is_its_reference_and_refuses_other_hints() {
        let div = div();
        assert_eq!(div.k_log(), 13);
        let mut rng = Rng(0xA5);
        for round in 0..300 {
            let (v1, v2) = (
                rng.word(),
                if round % 9 == 0 {
                    0
                } else {
                    rng.word() >> (rng.next() % 64)
                },
            );
            for &flags in &crate::rv::div::LEGAL {
                let (q, r) = semantics::div_hints(v1, v2, flags);
                let expected = [semantics::div(v1, v2, flags), 0];
                assert_eq!(
                    run(&div, &[v1, v2, flags, q, r], 5..7),
                    expected,
                    "div {flags:#x} of {v1:#x} by {v2:#x}"
                );
                // Any other quotient or remainder is refused, unless the divisor is zero,
                // where they are ignored and the result is still the specification's.
                let by_zero = if flags & crate::rv::div::WORD != 0 {
                    v2 as u32 == 0
                } else {
                    v2 == 0
                };
                for (q, r) in [
                    (q.wrapping_add(1), r),
                    (q, r.wrapping_add(1)),
                    (q ^ (1 << 63), r),
                    (rng.next(), rng.next()),
                ] {
                    let got = run(&div, &[v1, v2, flags, q, r], 5..7);
                    if by_zero {
                        assert_eq!(got, expected);
                    } else {
                        assert_eq!(got[1], 1, "div {flags:#x} of {v1:#x} by {v2:#x} accepts {q:#x}, {r:#x}");
                    }
                }
            }
        }
        // The forgery a check modulo 2^64 would accept: 1 / 3 with a quotient of (2^64 + 1) / 3.
        assert_eq!(run(&div, &[1, 3, 0, 0x5555_5555_5555_5555, 2], 5..7)[1], 1);
        // The overflow, and division by zero, as the specification has them.
        let min = i64::MIN as u64;
        let (q, r) = semantics::div_hints(min, u64::MAX, crate::rv::div::SIGNED);
        assert_eq!(
            run(&div, &[min, u64::MAX, crate::rv::div::SIGNED, q, r], 5..7),
            [min, 0]
        );
        assert_eq!(run(&div, &[7, 0, 0, 0, 0], 5..7), [u64::MAX, 0]);
        assert_eq!(run(&div, &[7, 0, crate::rv::div::REM, 0, 0], 5..7), [7, 0]);
    }

    #[test]
    fn blake2s_is_its_reference() {
        let circuit = blake2s();
        assert_eq!(circuit.k_log(), 14, "a compression is 256 packed words");
        let mut rng = Rng(0xA6);
        for round in 0..40 {
            let block: [u64; 16] = std::array::from_fn(|_| rng.word());
            let t = rng.word();
            // The legal flags, and now and then any finalization word, which the
            // circuit XORs in like the reference does.
            let flags = match round % 4 {
                0 => crate::rv::hash::FINAL,
                1 => rng.next() as u32 as u64,
                _ => 0,
            };
            let inputs: Vec<u64> = [t, flags]
                .into_iter()
                .chain(block[..4].iter().chain(&block[8..]).copied())
                .collect();
            let expected = if crate::rv::hash::LEGAL.contains(&flags) {
                semantics::blake2s(&block, t, flags)
            } else {
                let half = |w: &[u64]| -> Vec<u32> { w.iter().flat_map(|&w| [w as u32, (w >> 32) as u32]).collect() };
                let out = flock::hash::blake2s_compress(
                    &half(&block[..4]).try_into().unwrap(),
                    &half(&block[8..]).try_into().unwrap(),
                    t,
                    flags as u32,
                    0,
                );
                std::array::from_fn(|i| out[2 * i] as u64 | (out[2 * i + 1] as u64) << 32)
            };
            assert_eq!(run(&circuit, &inputs, 14..18), expected, "flags {flags:#x}");
        }
    }

    /// flock proves a batch of honest instances, and refuses one with a flipped output bit.
    #[test]
    fn alu_reduction_roundtrip() {
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let circuit = alu();
        let block = circuit.block();
        let n_log = 4;
        let mut rng = Rng(0xA2);
        let legal = crate::rv::alu::LEGAL;
        let rows: Vec<[u64; 4]> = (0..1 << n_log)
            .map(|i| [rng.word(), rng.word(), 0, legal[i % legal.len()]])
            .collect();
        let run = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = circuit.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let stage = block.prove_zerocheck(n_log, &z, &a, &b, &mut ps);
            let claim = block.prove_lincheck(n_log, stage, &z_lincheck, &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            block.verify(n_log, &mut vs).is_ok_and(|r| r.claim == claim) && vs.finish().is_ok()
        };
        assert!(run(None));
        // An output bit, a spare bit of `taken`'s word, a product.
        for bit in [
            64 * alu_ports::OUT + 5,
            64 * alu_ports::TAKEN + 1,
            circuit.useful_bits() - 1,
        ] {
            assert!(!run(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
