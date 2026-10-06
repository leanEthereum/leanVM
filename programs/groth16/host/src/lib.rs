//! The Groth16 program off the VM: proofs World Chain verified, laid out as the guest's advice,
//! and the output the guest must give.
//!
//! The proofs are `proofs.txt`: each the call World ID 4.0's `WorldIDVerifier` made to its
//! Groth16 verifier contract in one transaction, the proof compressed as the contract takes it.
//! The host decompresses the points as the contract does, so the guest reads `A`, `B` and `C`
//! whole and checks them itself.

use bn::{Fq, Fq2, G2};
use groth16::{G1Point, G2Point, Inputs, N_INPUTS, Proof};
use leanvm_guest::{PublicValues, as_words_unchecked};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../groth16.elf");

/// The proofs, with the transactions that carried them.
const PROOFS: &str = include_str!("../proofs.txt");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// A proof from the chain: the transaction that carried it, its block, the proof and its public
/// inputs.
pub struct Fixture {
    pub tx: &'static str,
    pub block: u64,
    pub proof: Proof,
    pub inputs: Inputs,
}

/// Every proof `proofs.txt` holds, in its order.
pub fn fixtures() -> Vec<Fixture> {
    PROOFS
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let mut fields = line.split_whitespace();
            let tx = fields.next().expect("a transaction");
            let block = fields.next().expect("a block").parse().expect("a block number");
            let words: Vec<[u64; 4]> = fields.map(word).collect();
            assert_eq!(words.len(), 4 + N_INPUTS, "{tx}: a compressed proof and its inputs");
            Fixture {
                tx,
                block,
                proof: decompress(&words[..4]),
                inputs: words[4..].try_into().expect("the inputs"),
            }
        })
        .collect()
}

/// `n` proofs, the fixtures in turn.
pub fn batch(n: usize) -> Run {
    // What the guest reads: the count, then each proof and its inputs.
    let mut advice = vec![n as u64];
    // What it commits: each proof's inputs.
    let mut public = PublicValues::new();
    for fixture in fixtures().iter().cycle().take(n) {
        groth16::verify(&fixture.proof, &fixture.inputs).expect("the chain's proofs verify");
        // SAFETY: `repr(C)` words, with no padding (see its definition).
        advice.extend(unsafe { as_words_unchecked(&fixture.proof) });
        advice.extend(fixture.inputs.as_flattened());
        public.commit(&fixture.inputs);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// A 256-bit word from its hex, as little-endian limbs.
fn word(hex: &str) -> [u64; 4] {
    let digits = hex.strip_prefix("0x").expect("a hex word");
    let padded = format!("{digits:0>64}");
    assert_eq!(padded.len(), 64, "a 256-bit word");
    std::array::from_fn(|i| u64::from_str_radix(&padded[64 - 16 * (i + 1)..64 - 16 * i], 16).expect("hex"))
}

/// `x >> k` for `k` in `1..64`.
fn shr(x: &[u64; 4], k: u32) -> [u64; 4] {
    std::array::from_fn(|i| x[i] >> k | x.get(i + 1).map_or(0, |high| high << (64 - k)))
}

/// A 256-bit word as big-endian bytes.
fn big_endian(limbs: &[u64; 4]) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (chunk, limb) in bytes.chunks_mut(8).zip(limbs.iter().rev()) {
        chunk.copy_from_slice(&limb.to_be_bytes());
    }
    bytes
}

fn fq(limbs: [u64; 4]) -> Fq {
    Fq::from_slice(&big_endian(&limbs)).expect("a coordinate below p")
}

fn limbs(x: Fq) -> [u64; 4] {
    let mut bytes = [0; 32];
    x.to_big_endian(&mut bytes).expect("32 bytes");
    std::array::from_fn(|i| u64::from_be_bytes(bytes[24 - 8 * i..32 - 8 * i].try_into().expect("8 bytes")))
}

/// `p`, little-endian limbs.
fn modulus() -> [u64; 4] {
    let mut bytes = [0; 32];
    Fq::modulus().to_big_endian(&mut bytes).expect("32 bytes");
    std::array::from_fn(|i| u64::from_be_bytes(bytes[24 - 8 * i..32 - 8 * i].try_into().expect("8 bytes")))
}

/// The contract's square root, `a^((p + 1) / 4)`, if `a` is a square.
fn sqrt(a: Fq) -> Option<Fq> {
    let mut exponent = modulus();
    exponent[0] += 1;
    let x = a.pow(fq(shr(&exponent, 2)));
    (x * x == a).then_some(x)
}

/// The contract's square root in `F_p2`: `hint` picks the sign of the norm's root.
fn sqrt2(a: Fq2, hint: bool) -> Option<Fq2> {
    let (a0, a1) = (a.real(), a.imaginary());
    let d = sqrt(a0 * a0 + a1 * a1)?;
    let d = if hint { -d } else { d };
    let two = Fq::one() + Fq::one();
    let x0 = sqrt((a0 + d) * two.inverse()?)?;
    let x = Fq2::new(x0, a1 * (x0 + x0).inverse()?);
    (x * x == a).then_some(x)
}

/// The contract's `decompress_g1`: `x` with the sign of `y` in its low bit.
fn decompress_g1(c: &[u64; 4]) -> G1Point {
    let x = fq(shr(c, 1));
    let y = sqrt(x * x * x + bn::G1::b()).expect("a point on G1");
    let y = if c[0] & 1 == 1 { -y } else { y };
    G1Point {
        x: limbs(x),
        y: limbs(y),
    }
}

/// The contract's `decompress_g2`: `x`'s real part with the hint and the sign in its low bits.
fn decompress_g2(c0: &[u64; 4], c1: &[u64; 4]) -> G2Point {
    let x = Fq2::new(fq(shr(c0, 2)), fq(*c1));
    let y = sqrt2(x * x * x + G2::b(), c0[0] & 2 == 2).expect("a point on the twist");
    let y = if c0[0] & 1 == 1 { -y } else { y };
    G2Point {
        x: [limbs(x.real()), limbs(x.imaginary())],
        y: [limbs(y.real()), limbs(y.imaginary())],
    }
}

/// The contract's compressed proof: `A`, `B`'s imaginary then real part of `x`, `C`.
fn decompress(words: &[[u64; 4]]) -> Proof {
    Proof {
        a: decompress_g1(&words[0]),
        b: decompress_g2(&words[2], &words[1]),
        c: decompress_g1(&words[3]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bn::{AffineG1, AffineG2, Fr, G1, GroupError, Gt, pairing_batch};
    use groth16::Error::{InputNotInField, NotInField, NotInSubgroup, NotOnCurve, Rejected};
    use groth16::vk;
    use leanvm_core::cpu::Program;
    use leanvm_core::rv::{Machine, Trap};
    use primitives::hash::{digest_words, hash};

    fn g1(p: &G1Point) -> G1 {
        AffineG1::new(fq(p.x), fq(p.y)).expect("a point of G1").into()
    }

    fn g2(p: &G2Point) -> G2 {
        let (x, y) = (Fq2::new(fq(p.x[0]), fq(p.x[1])), Fq2::new(fq(p.y[0]), fq(p.y[1])));
        AffineG2::new(x, y).expect("a point of G2").into()
    }

    /// The pairing check as Ethereum's precompile makes it (substrate-bn, the precompile's
    /// implementation in Parity's and Substrate's clients), with the guest's key.
    fn accepts(proof: &Proof, inputs: &Inputs) -> bool {
        let mut l = g1(&vk::IC[0]);
        for (x, base) in inputs.iter().zip(&vk::IC[1..]) {
            l = l + g1(base) * Fr::from_slice(&big_endian(x)).expect("an input below r");
        }
        pairing_batch(&[
            (g1(&proof.a), g2(&proof.b)),
            (g1(&proof.c), g2(&vk::DELTA_NEG)),
            (g1(&vk::ALPHA), g2(&vk::BETA_NEG)),
            (l, g2(&vk::GAMMA_NEG)),
        ]) == Gt::one()
    }

    /// `r`, the groups' order, little-endian limbs.
    const R: [u64; 4] = [
        0x43e1_f593_f000_0001,
        0x2833_e848_79b9_7091,
        0xb850_45b6_8181_585d,
        0x3064_4e72_e131_a029,
    ];

    fn negated(y: [u64; 4]) -> [u64; 4] {
        limbs(-fq(y))
    }

    #[test]
    fn the_chains_proofs_verify_and_nothing_near_them() {
        // Fixture: proofs World Chain accepted, from different transactions.
        let fixtures = fixtures();
        for f in &fixtures {
            assert!(accepts(&f.proof, &f.inputs), "{}: substrate-bn", f.tx);
            assert_eq!(groth16::verify(&f.proof, &f.inputs), Ok(()), "{}", f.tx);

            // Mutation: A negated, still on the curve.
            //
            //     e(-A, B) = e(A, B)^-1 → the product is e(A, B)^-2, not one
            let mut proof = f.proof;
            proof.a.y = negated(proof.a.y);
            assert!(!accepts(&proof, &f.inputs));
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);

            // Mutation: B negated, still in G2; then C.
            let mut proof = f.proof;
            proof.b.y = [negated(proof.b.y[0]), negated(proof.b.y[1])];
            assert!(!accepts(&proof, &f.inputs));
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);
            let mut proof = f.proof;
            proof.c.y = negated(proof.c.y);
            assert_eq!(groth16::verify(&proof, &f.inputs), Err(Rejected), "{}", f.tx);

            // Mutation: the low bit of each public input in turn.
            //
            //     L moves by IC[i + 1] → e(L, -gamma) changes
            for i in 0..N_INPUTS {
                let mut inputs = f.inputs;
                inputs[i][0] ^= 1;
                assert!(!accepts(&f.proof, &inputs));
                assert_eq!(groth16::verify(&f.proof, &inputs), Err(Rejected), "{}: input {i}", f.tx);
            }
        }
    }

    #[test]
    fn malformed_points_and_inputs_are_refused() {
        let f = &fixtures()[0];
        let refused = |proof: &Proof, inputs: &Inputs| groth16::verify(proof, inputs).unwrap_err();

        // A's x plus p: the same point mod p, but not canonical.
        let mut proof = f.proof;
        let mut carry = 0;
        for (x, p) in proof.a.x.iter_mut().zip(modulus()) {
            let sum = u128::from(*x) + u128::from(p) + carry;
            (*x, carry) = (sum as u64, sum >> 64);
        }
        assert_eq!(refused(&proof, &f.inputs), NotInField);

        // The point at infinity, as EIP-197 writes it, and points off their curves.
        let mut proof = f.proof;
        proof.c = G1Point { x: [0; 4], y: [0; 4] };
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);
        let mut proof = f.proof;
        proof.c.y[0] ^= 1;
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);
        let mut proof = f.proof;
        proof.b.x[1][0] ^= 1;
        assert_eq!(refused(&proof, &f.inputs), NotOnCurve);

        // B on the twist, outside G2: the first such x of the form k, as substrate-bn finds it.
        let (x, y) = (1..)
            .find_map(|k: u64| {
                let x = Fq2::new(fq([k, 0, 0, 0]), Fq::zero());
                let y = (x * x * x + G2::b()).sqrt()?;
                matches!(AffineG2::new(x, y), Err(GroupError::NotInSubgroup)).then_some((x, y))
            })
            .expect("a twist point outside G2");
        let mut proof = f.proof;
        proof.b = G2Point {
            x: [limbs(x.real()), limbs(x.imaginary())],
            y: [limbs(y.real()), limbs(y.imaginary())],
        };
        assert_eq!(refused(&proof, &f.inputs), NotInSubgroup);

        // An input equal to r, which reduces to zero.
        let mut inputs = f.inputs;
        inputs[3] = R;
        assert_eq!(refused(&f.proof, &inputs), InputNotInField);
    }

    /// Words as their little-endian bytes.
    fn bytes(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_accepts_the_chains_proofs_and_outputs_their_inputs() {
        // Invariant: the output is BLAKE2s-256 of the inputs, proof after proof.
        let fixtures = fixtures();
        let run = batch(fixtures.len());
        let inputs: Vec<u64> = fixtures.iter().flat_map(|f| f.inputs.as_flattened().to_vec()).collect();
        assert_eq!(run.expected, digest_words(&hash(&bytes(&inputs))));
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the last input's low bit.
        //
        //     the pairing check fails → the guest panics → an illegal instruction → no output
        let mut tampered = batch(1);
        *tampered.advice.last_mut().unwrap() ^= 1;
        assert!(on_the_vm(&tampered).is_err());

        // Mutation: A's y negated.
        let mut tampered = batch(1);
        let y = 1 + 4;
        let a_y: [u64; 4] = tampered.advice[y..y + 4].try_into().unwrap();
        tampered.advice[y..y + 4].copy_from_slice(&negated(a_y));
        assert!(on_the_vm(&tampered).is_err());
    }
}
