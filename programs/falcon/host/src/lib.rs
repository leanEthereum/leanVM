//! The Falcon-512 program off the VM: it signs, lays the signatures out as the guest's
//! advice, and verifies them natively for the output the guest must give.
//!
//! Signing is round-3 Falcon (PQClean's raw-message mode) and deterministic: a signer's key
//! and randomness are SHAKE256 streams of its index, so the advice, and the cycles, never move.
//!
//! One message for all signers is the Ethereum shape: validators attest to one block.

use falcon::{BODY_WORDS, Message, NONCE_WORDS, PUBLIC_KEY_WORDS, PublicKey, Signature};
use leanvm_guest::{PublicValues, as_words_unchecked};
use tide_fn_dsa::{
    CryptoRng, FALCON_KEYGEN_SEED_SIZE, FN_DSA_LOGN_512, FalconProfile, KeyPairGenerator512, RngCore, RngError,
    SHAKE256, SIGN_KEY_SIZE_512, SIGNATURE_SIZE_512, SigningKey, SigningKeyStandard, VRFY_KEY_SIZE_512,
};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../falcon.elf");

/// What one run of the guest is given, and what it must output.
pub struct Run {
    pub advice: Vec<u64>,
    pub expected: [u64; 4],
}

/// The message every signer signs.
const MESSAGE: Message = [0x4242_4242_4242_4242; 4];

/// The public key's header byte: a key of degree `2^9`.
const PUBLIC_KEY_HEADER: u8 = 0x09;
/// The signature's header byte: a compressed signature of degree `2^9`.
const SIGNATURE_HEADER: u8 = 0x39;

/// `n` signers, each with its own key, sign the message.
pub fn batch(n: usize) -> Run {
    // Keys and signatures are independent, so they are made in parallel.
    let signed = parallel::map_collect(n, |i| sign(i, &MESSAGE));
    // What the guest reads: the count, then key, message and signature for each.
    let mut advice = vec![n as u64];
    // What it commits: each claim, key and message.
    let mut public = PublicValues::new();
    for (pk, signature) in &signed {
        falcon::verify(pk, &MESSAGE, signature).expect("honest signatures verify");
        advice.extend(pk.h);
        advice.extend(MESSAGE);
        advice.extend(words_of_signature(signature));
        public.commit(&pk.h).commit(&MESSAGE);
    }
    Run {
        advice,
        expected: public.digest(),
    }
}

/// Signer `i`'s public key, and its signature on `message`.
fn sign(i: usize, message: &Message) -> (PublicKey, Signature) {
    // The key: PQClean's deterministic key generation, from a 48-byte seed.
    let mut seed = [0; FALCON_KEYGEN_SEED_SIZE];
    Stream::new(b"key", i).fill_bytes(&mut seed);
    let (mut sign_key, mut vrfy_key) = ([0; SIGN_KEY_SIZE_512], [0; VRFY_KEY_SIZE_512]);
    KeyPairGenerator512::default()
        .keygen_from_seed_pqclean(FN_DSA_LOGN_512, &seed, &mut sign_key, &mut vrfy_key)
        .expect("a 48-byte seed makes a key");

    // A 666-byte buffer holds the specification's padded format: the compressed s2 in at most 625 bytes.
    let mut signature = [0; SIGNATURE_SIZE_512];
    let len = SigningKeyStandard::decode(&sign_key)
        .expect("a fresh signing key decodes")
        .sign_falcon(
            &mut Stream::new(b"sign", i),
            FalconProfile::PqClean,
            &bytes(message),
            &mut signature,
        )
        .expect("signing succeeds");
    assert_eq!(signature[0], SIGNATURE_HEADER);
    (
        public_key(&vrfy_key),
        signature_of(&signature[1..41], &signature[41..len]),
    )
}

/// A key from its encoding: the header, then `h` packed.
fn public_key(encoding: &[u8; VRFY_KEY_SIZE_512]) -> PublicKey {
    assert_eq!(encoding[0], PUBLIC_KEY_HEADER);
    PublicKey {
        h: words::<PUBLIC_KEY_WORDS>(&encoding[1..], u64::from_be_bytes),
    }
}

/// A signature from its nonce and its compressed `s2`.
fn signature_of(nonce: &[u8], body: &[u8]) -> Signature {
    Signature {
        nonce: words::<NONCE_WORDS>(nonce, u64::from_le_bytes),
        body: words::<BODY_WORDS>(body, u64::from_be_bytes),
    }
}

/// Bytes as `W` words, zero past their end.
fn words<const W: usize>(bytes: &[u8], word: fn([u8; 8]) -> u64) -> [u64; W] {
    assert!(bytes.len() <= 8 * W, "{} bytes do not fit {W} words", bytes.len());
    let mut padded = [0; 8];
    let mut chunks = bytes.chunks(8);
    std::array::from_fn(|_| {
        let chunk = chunks.next().unwrap_or_default();
        padded = [0; 8];
        padded[..chunk.len()].copy_from_slice(chunk);
        word(padded)
    })
}

/// Words as their little-endian bytes.
fn bytes(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// A signature as the words the guest reads it from.
const fn words_of_signature(signature: &Signature) -> &[u64] {
    // SAFETY: `repr(C)` words, with no padding (see its definition).
    unsafe { as_words_unchecked(signature) }
}

/// A deterministic random stream: SHAKE256 of a label and an index.
struct Stream(SHAKE256);

impl Stream {
    fn new(label: &[u8], i: usize) -> Self {
        let mut shake = SHAKE256::new();
        shake.inject(label).expect("absorbing");
        shake.inject(&(i as u64).to_le_bytes()).expect("absorbing");
        shake.flip().expect("absorbing");
        Self(shake)
    }
}

impl RngCore for Stream {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }

    fn next_u64(&mut self) -> u64 {
        let mut b = [0; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.extract(dest).expect("squeezing");
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), RngError> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for Stream {}

#[cfg(test)]
mod tests {
    use super::*;
    use falcon::FalconVerifyError::{InvalidEncoding, InvalidPublicKey, TooLong};
    use falcon::{BODY_BYTES, N, Q, Shake256, ntt};
    use leanvm_core::cpu::Program;
    use leanvm_core::rv::{Machine, Trap};
    use primitives::hash::{digest_words, hash};
    use proptest::prelude::*;
    use std::collections::HashMap;

    /// The official known answers this crate carries: count, message, key, signed message.
    const KAT: &str = include_str!("../kat/falcon512-kat.rsp");

    /// One known answer: its key, its message as words, its signature.
    fn known_answers() -> Vec<(PublicKey, Vec<u64>, Signature)> {
        KAT.split("\n\n")
            .filter(|entry| entry.contains("pk = "))
            .map(|entry| {
                let fields: HashMap<&str, &str> = entry.lines().filter_map(|line| line.split_once(" = ")).collect();
                // NIST's signed message: the signature's length, the nonce, the message, then the
                // signature with header 0x29, its compressed s2 unpadded.
                let (pk, msg, sm) = (hex(fields["pk"]), hex(fields["msg"]), hex(fields["sm"]));
                let esig = &sm[2 + 40 + msg.len()..];
                assert_eq!(esig[0], 0x29);
                let message = msg
                    .chunks(8)
                    .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
                    .collect();
                (
                    public_key(pk.as_slice().try_into().unwrap()),
                    message,
                    signature_of(&sm[2..42], &esig[1..]),
                )
            })
            .collect()
    }

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn falcon_accepts_the_known_answers_and_nothing_near_them() {
        // NIST's round-3 vectors, made by the submitters' code: their verifier accepts each.
        let known = known_answers();
        assert_eq!(known.len(), 2);
        for (pk, message, signature) in &known {
            assert_eq!(falcon::verify(pk, message, signature), Ok(()));

            // Mutation: one bit of the message, of the nonce.
            //
            //     a new c = HashToPoint(r || m) → s1 = c - s2 * h is no longer short
            let mut other = message.clone();
            other[0] ^= 1;
            assert_eq!(falcon::verify(pk, &other, signature), Err(TooLong));
            let mut bad = signature.clone();
            bad.nonce[4] ^= 1 << 63;
            assert_eq!(falcon::verify(pk, message, &bad), Err(TooLong));

            // Mutation: the low bit of h's last coefficient, the last word's lowest bit.
            //
            //     h changes by 1 at x^511 → s2 * h by s2 x^511 → s1 by about ||s2||
            let mut other = *pk;
            other.h[PUBLIC_KEY_WORDS - 1] ^= 1;
            assert_eq!(falcon::verify(&other, message, signature), Err(TooLong));
        }
    }

    #[test]
    fn falcon_refuses_every_non_canonical_encoding() {
        // Fixture: a valid signature, whose body ends in zero bits.
        let (pk, signature) = sign(0, &MESSAGE);
        let verify = |pk: &PublicKey, body: [u64; BODY_WORDS]| {
            falcon::verify(
                pk,
                &MESSAGE,
                &Signature {
                    body,
                    ..signature.clone()
                },
            )
        };

        // Mutation: h's first coefficient set to q, its top 14 bits.
        let mut bad = pk;
        bad.h[0] = (bad.h[0] & (u64::MAX >> 14)) | ((Q as u64) << 50);
        assert_eq!(falcon::verify(&bad, &MESSAGE, &signature), Err(InvalidPublicKey));

        // Mutation: the first coefficient's encoding, each way it can be wrong.
        //
        //     -0           1 0000000 1        zero is never negative
        //     2048         0 0000000 0^16     a magnitude past 2047
        let (negative_zero, rest) = (0b1_0000_0001, signature.body[0] & (u64::MAX >> 9));
        let mut body = signature.body;
        body[0] = negative_zero << 55 | rest;
        assert_eq!(verify(&pk, body), Err(InvalidEncoding));
        body[0] = 0;
        assert_eq!(verify(&pk, body), Err(InvalidEncoding));

        // Mutation: one bit past the 625 bytes, one in the last word.
        //
        //     the padding must be zero, so each signature has one encoding
        for (word, bit) in [(BODY_BYTES / 8, 63 - 8 * (BODY_BYTES % 8)), (BODY_WORDS - 1, 0)] {
            let mut body = signature.body;
            body[word] |= 1 << bit;
            assert_eq!(verify(&pk, body), Err(InvalidEncoding));
        }
    }

    #[test]
    fn shake256_is_the_standard_one() {
        // FIPS 202's SHAKE256 of the empty message, its first 32 bytes.
        let mut out = Shake256::new().finalize();
        let lanes: Vec<u64> = (0..4).map(|_| out.next_lane()).collect();
        assert_eq!(
            bytes(&lanes),
            hex("46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f")
        );
    }

    proptest! {
        #[test]
        fn shake256_matches_a_reference(message in prop::collection::vec(any::<u64>(), 0..40)) {
            // Up to 40 words: absorbing crosses the 17-word rate twice, squeezing does too.
            let mut ours = Shake256::new();
            ours.absorb(&message);
            let mut ours = ours.finalize();
            let ours: Vec<u64> = (0..40).map(|_| ours.next_lane()).collect();

            let mut reference = SHAKE256::new();
            reference.inject(&bytes(&message)).unwrap();
            reference.flip().unwrap();
            let mut expected = vec![0; 8 * 40];
            reference.extract(&mut expected).unwrap();
            prop_assert_eq!(bytes(&ours), expected);
        }

        #[test]
        fn the_ntt_multiplies_mod_x512_plus_1(
            s2 in prop::collection::vec(prop_oneof![-2047i64..=2047, Just(-2047), Just(2047)], N),
            h in prop::collection::vec(prop_oneof![0..Q, Just(Q - 1)], N),
            c in prop::collection::vec(0..5 * Q, N),
        ) {
            // Fixture: s2 in [-2047, 2047] and h in [0, q), often at their extremes: the widest inputs the bounds assume.
            let (s2, h): ([i64; N], [i64; N]) = (s2.try_into().unwrap(), h.try_into().unwrap());
            let (mut a, mut b) = (s2, h);

            // The verifier's product: two forward transforms, then the inverse with the pointwise product.
            ntt::multiply(&mut a, &mut b);

            // Invariant: each coefficient is the schoolbook negacyclic product's, mod q.
            //
            //     x^i * x^j = x^(i+j), or -x^(i+j-512) past degree 511
            let mut expected = [0i64; N];
            for (i, &a) in s2.iter().enumerate() {
                for (j, &b) in h.iter().enumerate() {
                    let (k, sign) = if i + j < N { (i + j, 1) } else { (i + j - N, -1) };
                    expected[k] += sign * a * b;
                }
            }

            // c - (s2 * h)_i, for c anywhere in [0, 5q) as hash-to-point leaves it, is the centered residue.
            //
            //     about one coefficient in a thousand takes the wrap past q/2
            for ((&p, &e), &c) in a.iter().zip(&expected).zip(&c) {
                let residue = (c - e).rem_euclid(Q);
                let centered = if residue > Q / 2 { residue - Q } else { residue };
                prop_assert_eq!(ntt::sub_centered(c, p), centered);
            }
        }
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_outputs_the_blake2s_of_its_claims() {
        // Invariant: the output is BLAKE2s-256 of the claims (key, message: 116 words) back to back.
        let claim = PUBLIC_KEY_WORDS + MESSAGE.len();
        let entry = claim + size_of::<Signature>() / 8;
        for n in 0..=2 {
            let run = batch(n);
            assert_eq!(run.advice.len(), 1 + n * entry);
            let claims: Vec<u64> = run.advice[1..]
                .chunks(entry)
                .flat_map(|e| e[..claim].to_vec())
                .collect();
            let expected = digest_words(&hash(&bytes(&claims)));
            assert_eq!(run.expected, expected, "{n} claims, natively");
            assert_eq!(on_the_vm(&run), Ok(expected), "{n} claims, on the VM");
        }

        // Mutation: the low bit of the last body word, which must be zero.
        //
        //     the guest's check fails → it panics → an illegal instruction → no output
        let mut run = batch(1);
        *run.advice.last_mut().unwrap() ^= 1;
        assert!(on_the_vm(&run).is_err());
    }
}
