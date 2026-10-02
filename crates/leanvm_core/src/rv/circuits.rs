//! Each instruction class's function as a flock gate list.
//!
//! A circuit's ports are whole 64-bit words.
//!
//! They are the words its table puts on the bus: register values, the immediate, the flags, the result.
//!
//! A circuit is defined on its class's legal flag words only.
//!
//! Those words are one-hot where they select, so a selection is an XOR of products.
//!
//! What the Rust and Python circuits must agree on is the port layout and the order products are made in.
//!
//! Only products are committed, so only products cost.
//!
//! An XOR, a NOT or a copy is free.

use super::semantics::{Alu, Div, Hash, Load, Mul, Mulh, Shift, Store};
use flock::arith::mul::Multiplier;
use flock::circuit::{Builder, Circuit, Wire};
use primitives::hash::{G_LANES, IV, SIGMA};
use std::sync::OnceLock;

/// A class's circuit: its function as a gate list over the words its table puts on the bus.
///
/// The gate list reads the input words, then writes the output words, in the order the class declares them.
pub trait ClassCircuit {
    /// The class's gate list.
    fn circuit() -> Circuit;
}

impl ClassCircuit for Alu {
    /// The ALU: `(v1, v2, imm, flags) -> (out, taken)`.
    ///
    /// It mirrors the reference function on every legal flag word.
    ///
    /// - The second operand is `b = v2 ^ imm`.
    /// - One adder gives `v1 + b`, or `v1 - b` for the comparisons.
    /// - The output is that sum, unless a selector picks a comparison or a bitwise operation.
    /// - The jump is taken always, or when the one branch condition set holds.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 15], &[64, 1]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let b = c.xor_word(&v2, &imm);

        // The difference is v1 + !b + 1.
        //
        // It borrows exactly when that sum does not carry out.
        let sub = flag(Self::SUB);
        let b_or_not: Word = b.iter().map(|&bit| c.xor(bit, sub)).collect();
        let (sum, carry_out) = c.add_with_carry(&v1, &b_or_not, sub);

        // The comparisons, from the borrow and the signs.
        //
        //     ltu = borrow
        //     lt  = borrow ^ sign(v1) ^ sign(b)
        //     eq  = no bit of v1 ^ b set
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], b[63]);
        let lt = c.xor(ltu, signs);
        let diff = c.xor_word(&v1, &b);
        let ne = c.any(&diff);
        let eq = c.not(ne);

        // The output: the sum unless a selector is set.
        //
        //     and = v1 * b
        //     or  = v1 * b ^ (v1 ^ b)
        //     xor = v1 ^ b
        let sum = c.sext32_if(flag(Self::WORD), &sum);
        let selectors = [Self::SEL_LT, Self::SEL_LTU, Self::SEL_AND, Self::SEL_OR, Self::SEL_XOR];
        let none = selectors.iter().fold(c.one(), |acc, &s| c.xor(acc, flag(s)));
        let and_or = c.xor(flag(Self::SEL_AND), flag(Self::SEL_OR));
        let or_xor = c.xor(flag(Self::SEL_OR), flag(Self::SEL_XOR));
        let mut out = c.and_word(none, &sum);
        for i in 0..64 {
            let both = c.and(v1[i], b[i]);
            let and_term = c.and(and_or, both);
            let xor_term = c.and(or_xor, diff[i]);
            let logic = c.xor(and_term, xor_term);
            out[i] = c.xor(out[i], logic);
        }

        // A comparison is a single bit, the output's bit 0.
        let lt_term = c.and(flag(Self::SEL_LT), lt);
        let ltu_term = c.and(flag(Self::SEL_LTU), ltu);
        let compared = c.xor(lt_term, ltu_term);
        out[0] = c.xor(out[0], compared);

        // A JALR target drops its low bit.
        let keep_bit0 = c.not(flag(Self::CLEAR_BIT0));
        out[0] = c.and(keep_bit0, out[0]);

        // The jump: unconditional, or the one branch condition set.
        let (ge, geu) = (c.not(lt), c.not(ltu));
        let taken = [
            (Self::BR_EQ, eq),
            (Self::BR_NE, ne),
            (Self::BR_LT, lt),
            (Self::BR_GE, ge),
            (Self::BR_LTU, ltu),
            (Self::BR_GEU, geu),
        ]
        .into_iter()
        .fold(flag(Self::ALWAYS), |acc, (when, holds)| {
            let term = c.and(flag(when), holds);
            c.xor(acc, term)
        });

        c.output_word(0, &out);
        c.output(1, 0, taken);
        c.finish()
    }
}

impl ClassCircuit for Shift {
    /// The shifter: `(v1, v2, imm, flags) -> out`.
    ///
    /// One right shifter serves both directions.
    ///
    /// A left shift is a right shift of the bit-reversed word, reversed back.
    ///
    /// The right shift is six barrel stages, by 1, 2, 4, 8, 16 and 32 bits.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let (right, arith, word) = (flag(Self::RIGHT), flag(Self::ARITH), flag(Self::WORD));

        // The amount: six bits, or five for a word shift.
        let mut amount: Word = (0..6).map(|i| c.xor(v2[i], imm[i])).collect();
        let not_word = c.not(word);
        amount[5] = c.and(not_word, amount[5]);

        // A word shift takes the low 32 bits, extended by the sign if arithmetic, by zero if not.
        let low_sign = c.and(arith, v1[31]);
        let x: Word = (0..64)
            .map(|i| if i < 32 { v1[i] } else { c.mux(word, low_sign, v1[i]) })
            .collect();

        // What a right shift brings in from the top; arithmetic implies right.
        let fill = c.and(arith, x[63]);

        // Reverse, shift right stage by stage, reverse back.
        let mut y = c.reverse_unless(right, &x);
        for (stage, &bit) in amount.iter().enumerate() {
            let by = 1 << stage;
            y = (0..64)
                .map(|i| c.mux(bit, if i + by < 64 { y[i + by] } else { fill }, y[i]))
                .collect();
        }
        let y = c.reverse_unless(right, &y);

        let out = c.sext32_if(word, &y);
        c.output_word(0, &out);
        c.finish()
    }
}

impl ClassCircuit for Load {
    /// The load: `(v1, imm, flags, cell) -> (address, out)`.
    ///
    /// The address is what goes on the memory bus, and `cell` is the word read there.
    ///
    /// - The cell shifts right until the addressed byte is at the bottom.
    /// - The output keeps the access's width, extended by its top bit if the load is signed.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 3, 64], &[64, 64]);
        let (v1, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let address = c.add_wrapping(&v1, &imm);
        let [ge2, ge4, eq8] = c.width_thresholds(&flags[..2]);
        let bus = c.bus_address(&address, [ge2, ge4, eq8]);
        let value = c.shift_bytes(&cell, &address[..3], false);

        // The extension: the value's top bit, where the width places it, if the load is signed.
        //
        //     width 1   bit 7
        //     width 2   bit 15
        //     width 4   bit 31
        let (w1, w2, w4) = (c.not(ge2), c.xor(ge2, ge4), c.xor(ge4, eq8));
        let sign = [(w1, 7), (w2, 15), (w4, 31)]
            .into_iter()
            .fold(None, |acc, (width, bit)| {
                let term = c.and(width, value[bit]);
                c.xor(acc, term)
            });
        let extension = c.and(flags[2], sign);
        c.output_word(0, &bus);

        // Each byte above the first is the value's if the width reaches it, else the extension.
        for (i, &bit) in value.iter().enumerate() {
            let keeps = match i {
                0..8 => None,
                8..16 => Some(ge2),
                16..32 => Some(ge4),
                _ => Some(eq8),
            };
            let wire = keeps.map_or(bit, |keeps| c.mux(keeps, bit, extension));
            c.output(1, i, wire);
        }
        c.finish()
    }
}

impl ClassCircuit for Store {
    /// The store: `(v1, v2, imm, flags, cell) -> (address, new cell)`.
    ///
    /// The value shifts up to the addressed bytes, which replace the cell's.
    ///
    /// The cell's other bytes are kept.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 2, 64], &[64, 64]);
        let (v1, v2, imm, flags, cell) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
        let address = c.add_wrapping(&v1, &imm);
        let [ge2, ge4, eq8] = c.width_thresholds(&flags);
        let bus = c.bus_address(&address, [ge2, ge4, eq8]);
        let value = c.shift_bytes(&v2, &address[..3], true);

        // Byte j is written when it shares the access's block of 2^log_width bytes.
        //
        // That is: bit k of j equals bit k of the address, wherever the width does not span both.
        let spans: [[Wire; 2]; 3] = std::array::from_fn(|k| {
            let (is_zero, threshold) = (c.not(address[k]), [ge2, ge4, eq8][k]);
            [c.or(is_zero, threshold), c.or(address[k], threshold)]
        });
        c.output_word(0, &bus);

        // Each byte is the value's if written, else the cell's.
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
}

impl ClassCircuit for Mul {
    /// The low word of the product: `(v1, v2, flags) -> out`.
    ///
    /// A word multiplication sign-extends the low 32 bits.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 1], &[64]);
        let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
        let (product, _) = Multiplier::build(&mut c, &v1, &v2, 64);
        let out = c.sext32_if(f[0], &product);
        c.output_word(0, &out);
        c.finish()
    }
}

impl ClassCircuit for Mulh {
    /// The high word of the product: `(v1, v2, flags) -> out`.
    ///
    /// A negative operand reads as its unsigned value minus `2^64`.
    ///
    /// So the signed high word is the unsigned one, corrected:
    ///
    /// ```text
    ///     high(v1 * v2) = high_u(v1 * v2) - [v1 < 0] * v2 - [v2 < 0] * v1    (mod 2^64)
    /// ```
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 2], &[64]);
        let (v1, v2, f) = (c.input(0), c.input(1), c.input(2));
        let (product, _) = Multiplier::build(&mut c, &v1, &v2, 128);
        let mut high = product[64..].to_vec();

        // Subtract the other operand for each signed negative one.
        for (signed, operand, other) in [(f[0], &v1, &v2), (f[1], &v2, &v1)] {
            let negative = c.and(signed, operand[63]);

            // high - other is high + !other + 1, all of it gated by negative.
            let subtrahend: Word = other
                .iter()
                .map(|&bit| {
                    let inverted = c.not(bit);
                    c.and(negative, inverted)
                })
                .collect();
            (high, _) = c.add_with_carry(&high, &subtrahend, negative);
        }

        c.output_word(0, &high);
        c.finish()
    }
}

impl ClassCircuit for Div {
    /// The division: `(v1, v2, flags, q, r) -> (out, bad)`.
    ///
    /// The prover supplies `q` and `r`, the magnitudes of the quotient and the remainder.
    ///
    /// The circuit sets `bad` unless they are the right ones:
    ///
    /// ```text
    ///     |n| = q * |d| + r
    ///     r   < |d|
    /// ```
    ///
    /// The identity holds over the integers: the product has no high word, and the sum no carry.
    ///
    /// A row puts `bad` where its bytecode entry holds zero, so the proof forces it to zero.
    ///
    /// A zero divisor checks nothing, and gives what RISC-V says: all ones, or the dividend.
    ///
    /// The one overflow, `-2^63 / -1`, needs no special case on magnitudes.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 3, 64, 64], &[64, 1]);
        let (v1, v2, f, q, r) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
        let (signed, rem, word) = (f[0], f[1], f[2]);

        // A word division divides the low 32 bits, extended as the division is signed or not.
        let mut extend = |x: &[Wire]| -> Word {
            let sign = c.and(signed, x[31]);
            (0..64)
                .map(|i| if i < 32 { x[i] } else { c.mux(word, sign, x[i]) })
                .collect()
        };
        let (n, d) = (extend(&v1), extend(&v2));

        // The operands' magnitudes.
        let (n_negative, d_negative) = (c.and(signed, n[63]), c.and(signed, d[63]));
        let (n_abs, d_abs) = (c.negate_if(n_negative, &n), c.negate_if(d_negative, &d));

        // Check |n| = q * |d| + r: the product fits 64 bits, the sum does not carry, and it equals |n|.
        let (product, _) = Multiplier::build(&mut c, &q, &d_abs, 128);
        let overflows = c.any(&product[64..]);
        let (sum, carries) = c.add_with_carry(&product[..64], &r, None);
        let difference = c.xor_word(&sum, &n_abs);
        let differs = c.any(&difference);

        // Check r < |d|: r - |d| = r + !|d| + 1 carries out exactly when r >= |d|.
        let d_inverted: Word = d_abs.iter().map(|&bit| c.not(bit)).collect();
        let one = c.one();
        let (_, too_large) = c.add_with_carry(&r, &d_inverted, one);

        // Any failed check is bad, unless the divisor is zero.
        let d_nonzero = c.any(&d);
        let wrong = [carries, differs, too_large]
            .into_iter()
            .fold(overflows, |acc, w| c.or(acc, w));
        let bad = c.and(d_nonzero, wrong);

        // The quotient is negative when the operands' signs differ.
        // The remainder is negative when the dividend is.
        let q_negative = c.xor(n_negative, d_negative);
        let (q_signed, r_signed) = (c.negate_if(q_negative, &q), c.negate_if(n_negative, &r));

        // The output: the quotient or the remainder, or the zero divisor's result.
        let out: Word = (0..64)
            .map(|i| {
                let result = c.mux(rem, r_signed[i], q_signed[i]);
                let by_zero = c.mux(rem, n[i], one);
                c.mux(d_nonzero, result, by_zero)
            })
            .collect();
        let out = c.sext32_if(word, &out);

        c.output_word(0, &out);
        c.output(1, 0, bad);
        c.finish()
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

/// A word of wires, low bit first.
type Word = Vec<Wire>;

/// Word operations on a gate builder.
///
/// A gadget makes its products in a fixed order.
///
/// The Python verifier mirrors that order, so a gadget's loop order is part of the circuit.
trait WordGadgets {
    /// `x ^ y`, bit by bit; no product.
    fn xor_word(&mut self, x: &[Wire], y: &[Wire]) -> Word;

    /// `s * x`, bit by bit; one product per bit.
    fn and_word(&mut self, s: Wire, x: &[Wire]) -> Word;

    /// Whether any bit of `x` is set; one product per OR.
    fn any(&mut self, x: &[Wire]) -> Wire;

    /// `x + y + carry_in`, and the carry out of the top bit; one product per bit.
    fn add_with_carry(&mut self, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire);

    /// `x + y` modulo `2^width`; one product per bit but the top.
    fn add_wrapping(&mut self, x: &[Wire], y: &[Wire]) -> Word;

    /// `-x` if `negative`, else `x`; one product per bit.
    fn negate_if(&mut self, negative: Wire, x: &[Wire]) -> Word;

    /// `x`, bits 32 to 63 replaced by bit 31 when `word` is set; one product per high bit.
    fn sext32_if(&mut self, word: Wire, x: &[Wire]) -> Word;

    /// Commit `x` as output port `port`.
    fn output_word(&mut self, port: usize, x: &[Wire]);

    /// `x` bit-reversed unless `right` is set; one product per bit.
    fn reverse_unless(&mut self, right: Wire, x: &[Wire]) -> Word;

    /// The width thresholds, from the two bits of the width's logarithm: at least 2, at least 4, exactly 8.
    fn width_thresholds(&mut self, log_width: &[Wire]) -> [Wire; 3];

    /// The bus address: the address, its low three bits kept only where they misalign the access.
    ///
    /// It is the reference's bus address, bit by bit.
    fn bus_address(&mut self, address: &[Wire], thresholds: [Wire; 3]) -> Word;

    /// `x` shifted by `8 * amount` bits, left or right; `amount` has three bits.
    fn shift_bytes(&mut self, x: &[Wire], amount: &[Wire], left: bool) -> Word;
}

impl WordGadgets for Builder {
    fn xor_word(&mut self, x: &[Wire], y: &[Wire]) -> Word {
        x.iter().zip(y).map(|(&x, &y)| self.xor(x, y)).collect()
    }

    fn and_word(&mut self, s: Wire, x: &[Wire]) -> Word {
        x.iter().map(|&x| self.and(s, x)).collect()
    }

    fn any(&mut self, x: &[Wire]) -> Wire {
        x.iter().fold(None, |acc, &bit| self.or(acc, bit))
    }

    fn add_with_carry(&mut self, x: &[Wire], y: &[Wire], carry_in: Wire) -> (Word, Wire) {
        let mut carry = carry_in;
        let mut sum = Vec::with_capacity(x.len());
        for (&x, &y) in x.iter().zip(y) {
            // The sum bit is x ^ y ^ c.
            let xc = self.xor(x, carry);
            let yc = self.xor(y, carry);
            sum.push(self.xor(xc, y));

            // The carry out is maj(x, y, c) = ((x ^ c)(y ^ c)) ^ c.
            let maj = self.and(xc, yc);
            carry = self.xor(maj, carry);
        }
        (sum, carry)
    }

    fn add_wrapping(&mut self, x: &[Wire], y: &[Wire]) -> Word {
        let (mut carry, width) = (None, x.len());
        let mut sum = Vec::with_capacity(width);
        for (i, (&x, &y)) in x.iter().zip(y).enumerate() {
            // The sum bit is x ^ y ^ c.
            let xc = self.xor(x, carry);
            let yc = self.xor(y, carry);
            sum.push(self.xor(xc, y));

            // The carry out of the top bit falls off the modulus, so it is never made.
            if i + 1 < width {
                let maj = self.and(xc, yc);
                carry = self.xor(maj, carry);
            }
        }
        sum
    }

    fn negate_if(&mut self, negative: Wire, x: &[Wire]) -> Word {
        // Two's complement: (x ^ negative) + negative.
        let flipped: Word = x.iter().map(|&bit| self.xor(bit, negative)).collect();
        self.add_with_carry(&flipped, &[None; 64], negative).0
    }

    fn sext32_if(&mut self, word: Wire, x: &[Wire]) -> Word {
        (0..64)
            .map(|i| if i < 32 { x[i] } else { self.mux(word, x[31], x[i]) })
            .collect()
    }

    fn output_word(&mut self, port: usize, x: &[Wire]) {
        for (bit, &wire) in x.iter().enumerate() {
            self.output(port, bit, wire);
        }
    }

    fn reverse_unless(&mut self, right: Wire, x: &[Wire]) -> Word {
        (0..64).map(|i| self.mux(right, x[i], x[63 - i])).collect()
    }

    fn width_thresholds(&mut self, log_width: &[Wire]) -> [Wire; 3] {
        [
            self.or(log_width[0], log_width[1]),
            log_width[1],
            self.and(log_width[0], log_width[1]),
        ]
    }

    fn bus_address(&mut self, address: &[Wire], thresholds: [Wire; 3]) -> Word {
        (0..64)
            .map(|i| {
                if i < 3 {
                    self.and(address[i], thresholds[i])
                } else {
                    address[i]
                }
            })
            .collect()
    }

    fn shift_bytes(&mut self, x: &[Wire], amount: &[Wire], left: bool) -> Word {
        let mut x = x.to_vec();
        for (stage, &bit) in amount.iter().enumerate() {
            // Stage k moves by 8 * 2^k bits when bit k is set; a vacated bit is zero.
            let by = 8 << stage;
            let from = |x: &[Wire], i: usize| {
                if left {
                    i.checked_sub(by).and_then(|j| x[j])
                } else {
                    x.get(i + by).copied().flatten()
                }
            };
            x = (0..64).map(|i| self.mux(bit, from(&x, i), x[i])).collect();
        }
        x
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
    use crate::rv::entry::Class;
    use crate::rv::semantics::tests::edge_word;
    use crate::rv::semantics::{InstructionClass, WordAccess};
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use proptest::prelude::*;
    use proptest::strategy::ValueTree;
    use proptest::test_runner::{Config, TestRunner};
    use std::fmt::Debug;
    use std::sync::LazyLock;

    /// Every class with a circuit.
    const CLASSES: [Class; 8] = [
        Class::Alu,
        Class::Shift,
        Class::Load,
        Class::Store,
        Class::Mul,
        Class::Mulh,
        Class::Div,
        Class::Hash,
    ];

    // The circuits a test drives directly, built once.
    static ALU: LazyLock<Circuit> = LazyLock::new(Alu::circuit);
    static STORE: LazyLock<Circuit> = LazyLock::new(Store::circuit);
    static DIV: LazyLock<Circuit> = LazyLock::new(Div::circuit);
    static BLAKE2S: LazyLock<Circuit> = LazyLock::new(Hash::circuit);

    /// The circuit's first `n` output words on `inputs`, read off the witness the gate walk writes.
    fn run(circuit: &Circuit, inputs: &[u64], n: usize) -> Vec<u64> {
        // One instance's tables, zeroed.
        let words = 1 << (circuit.k_log() - 6);
        let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);

        // The output ports follow the input ports in the instance's words.
        circuit.witness_instance(inputs, &mut z, &mut az, &mut bz);
        let first = circuit.n_input_words();
        z[first..first + n].to_vec()
    }

    /// Check a class: its dispatch, then `cases` random instances on which its circuit computes its reference function.
    fn circuit_matches_reference<C: InstructionClass + Arbitrary + Debug>(cases: u32) {
        let circuit = C::circuit();

        // The runtime dispatch on the class names this type's flags and circuit.
        assert_eq!(C::CLASS.legal_flags(), C::LEGAL);
        assert_eq!(C::CLASS.circuit().useful_bits(), circuit.useful_bits());

        let mut runner = TestRunner::new(Config::with_cases(cases));
        runner
            .run(&any::<C>(), |instance| {
                // The reference's output words, against the circuit's on the instance's input words.
                let expected = C::output_words(&instance.eval());
                prop_assert_eq!(run(&circuit, &instance.input_words(), expected.len()), expected);
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn instance_sizes_are_pinned() {
        // The log of each instance's bits, which the tables fix before any circuit is built.
        let sizes = CLASSES.map(|class| class.circuit().k_log());
        assert_eq!(sizes, [10, 10, 10, 10, 12, 13, 13, 14]);
    }

    #[test]
    fn every_circuit_matches_its_reference() {
        // The cheap circuits get more cases, the large ones fewer.
        circuit_matches_reference::<Alu>(4096);
        circuit_matches_reference::<Shift>(4096);
        circuit_matches_reference::<Load>(4096);
        circuit_matches_reference::<Store>(4096);
        circuit_matches_reference::<Mul>(512);
        circuit_matches_reference::<Mulh>(512);
        circuit_matches_reference::<Div>(512);
        circuit_matches_reference::<Hash>(64);
    }

    proptest! {
        #[test]
        fn a_misaligned_store_names_no_cell(store in any::<Store>(), offset in 1u64..8) {
            // Mutation: misalign an aligned store, by an offset its width does not divide.
            let store = Store { v1: store.v1 | offset, ..store };
            let log_width = store.flags & Store::LOG_WIDTH;
            prop_assume!(!WordAccess::is_aligned(store.v1.wrapping_add(store.imm), log_width));

            // The bus address is still the reference's, and names no cell.
            let (address, _) = store.eval();
            prop_assert_eq!(run(&STORE, &store.input_words(), 1), vec![address]);
            prop_assert!(!address.is_multiple_of(8));
        }

        #[test]
        fn div_refuses_any_other_hint(div in any::<Div>(), dq in any::<u64>(), dr in any::<u64>()) {
            // Mutation: shift the honest hints by a nonzero amount.
            prop_assume!((dq, dr) != (0, 0));
            let mut inputs = div.input_words();
            inputs[3] = inputs[3].wrapping_add(dq);
            inputs[4] = inputs[4].wrapping_add(dr);
            let got = run(&DIV, &inputs, 2);

            // A nonzero divisor refuses them; a zero divisor ignores them.
            let by_zero = if div.flags & Div::WORD != 0 { div.v2 as u32 == 0 } else { div.v2 == 0 };
            if by_zero {
                prop_assert_eq!(got, Div::output_words(&div.eval()));
            } else {
                prop_assert_eq!(got[1], 1);
            }
        }

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

    #[test]
    fn division_edge_cases_match_the_reference() {
        // The signed overflow -2^63 / -1, and a zero divisor for the quotient and the remainder.
        let min = i64::MIN as u64;
        for div in [
            Div {
                flags: Div::SIGNED,
                v1: min,
                v2: u64::MAX,
            },
            Div { flags: 0, v1: 7, v2: 0 },
            Div {
                flags: Div::REM,
                v1: 7,
                v2: 0,
            },
        ] {
            assert_eq!(
                run(&DIV, &div.input_words(), 2),
                Div::output_words(&div.eval()),
                "{div:?}"
            );
        }
    }

    #[test]
    fn a_hint_correct_modulo_2_64_is_refused() {
        // 1 / 3 with q = (2^64 + 1) / 3: q * 3 = 2^64 + 1, which is 1 modulo 2^64.
        assert_eq!(run(&DIV, &[1, 3, 0, 0x5555_5555_5555_5555, 2], 2)[1], 1);
    }

    #[test]
    fn flock_proves_honest_alu_instances_and_refuses_a_flipped_bit() {
        // Fixture: 16 instances cycling through the legal words.
        const LABEL: &[u8] = b"rv-alu-reduction-test";
        let block = ALU.block();
        let n_log = 4;
        let rows: Vec<[u64; 4]> = (0..1u64 << n_log)
            .map(|i| {
                [
                    i.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    !i,
                    0,
                    Alu::LEGAL[i as usize % Alu::LEGAL.len()],
                ]
            })
            .collect();

        // Prove the batch, optionally flipping one witness bit first, and verify.
        let accepts = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = ALU.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let instance = flock::reduction::Instance {
                block,
                n_blocks_log: n_log,
                z: &z,
                a: &a,
                b: &b,
                pad: None,
                z_lincheck: &z_lincheck,
            };
            let claims = flock::reduction::prove(&[instance], &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            flock::reduction::verify(&[(block, n_log)], &mut vs).is_ok_and(|r| r[0].claim == claims[0])
                && vs.finish().is_ok()
        };
        assert!(accepts(None));

        // Mutation: an output bit, a spare bit of taken's word, the last product.
        for bit in [
            64 * ALU.n_input_words() + 5,
            64 * (ALU.n_input_words() + 1) + 1,
            ALU.useful_bits() - 1,
        ] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }

    #[test]
    fn every_bitsliced_witness_is_the_one_instance_walk() {
        // Invariant: the 64-lane walk the prover runs writes what the one-instance walk writes.
        //
        // Fixture: 128 instances per circuit, so two 64-lane walks.
        let n_log = 7;
        let mut runner = TestRunner::deterministic();
        for circuit in CLASSES.map(Class::circuit) {
            // Edge-biased words drive every carry and comparison.
            let mut draw = || edge_word().new_tree(&mut runner).unwrap().current();
            let rows: Vec<Vec<u64>> = (0..1 << n_log)
                .map(|_| (0..circuit.n_input_words()).map(|_| draw()).collect())
                .collect();

            // The same batch through both generators, every table compared.
            let walk = circuit.generate_witness_with(&rows, &rows[0], 1 << n_log, &mut [], |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz);
            });
            let sliced = circuit.generate_witness_from(&rows, &rows[0], 1 << n_log, &mut [], |row, words| {
                words.copy_from_slice(row);
            });
            assert!(walk.0[..] == sliced.0[..], "z");
            assert!(walk.1[..] == sliced.1[..], "A*z");
            assert!(walk.2[..] == sliced.2[..], "B*z");
            assert!(walk.3[..] == sliced.3[..], "lincheck stripes");
        }
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
        let fast = BLAKE2S.generate_witness_with(&rows, &[0; 14], 1 << n_log, &mut [], |row, z, az, bz| {
            blake2s_witness(row, z, az, bz);
        });
        assert!(walk.0[..] == fast.0[..], "z");
        assert!(walk.1[..] == fast.1[..], "A*z");
        assert!(walk.2[..] == fast.2[..], "B*z");
        assert!(walk.3[..] == fast.3[..], "lincheck stripes");
    }
}
