//! The leanDA program off the VM: what a block builder computes, then lays out as the
//! guest's advice, and the guest's own library run natively for the output the guest must give.
//!
//! The builder encodes the blobs and commits to them.
//!
//! The dual codeword `L` then follows from the root, by Fiat-Shamir.

use primitives::PrimeCharacteristicRing;

use fiat_shamir::merkle::hash_to_scalars;
use fiat_shamir::{DS_OBSERVE, DS_SQUEEZE, compress, digest_words};
use leanda::{CELLS, Dual, Hash, LOG_K, M};
use leanvm_guest::{PublicValues, Run};
use pcs::ntt::AdditiveNttF64;
use primitives::{F64, F192};

/// The guest (`../guest`), built by `programs/build.sh`.
pub const ELF: &[u8] = include_bytes!("../../leanda.elf");

/// Transcript label, so a membership challenge is never any other challenge.
const LABEL: &[u8] = b"leanDA/rs-membership/v1";

/// `n` blobs of 128 KiB, encoded and committed to.
pub fn blobs(n: usize) -> Run {
    // The builder: encode, commit, then derive `L` from the root.
    let codewords = encode(&payload(n));
    let rows = codewords.as_chunks::<M>().0;
    let mut cells = vec![[[0; 4]; CELLS]; n.next_power_of_two()];
    let root = leanda::commit(rows, &mut cells).expect("1..=MAX_ROWS blobs");
    let dual = dual_codeword(&root);
    // The guest commits what its code computes natively: the root and `H(L)`.
    let checked = leanda::check(dual.as_slice().try_into().unwrap(), rows, &mut cells).expect("codewords");

    // The advice: the blob count, `L`, then the encoded blobs.
    let mut advice = vec![n as u64];
    advice.extend_from_slice(dual.as_flattened());
    advice.extend_from_slice(&codewords);
    let mut public = PublicValues::new();
    public.commit(&checked);
    Run {
        advice,
        expected: public.digest(),
    }
}

/// Blobs of any payload: a Weyl sequence, one symbol per step.
fn payload(n: usize) -> Vec<u64> {
    (1..=n << LOG_K)
        .map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64))
        .collect()
}

/// Encode each blob of `k` symbols to `m`, systematically: the blob is the first half.
///
/// The inverse NTT interpolates the blob, and the NTT evaluates it on the whole domain.
fn encode(payload: &[u64]) -> Vec<u64> {
    let interpolation = AdditiveNttF64::standard(LOG_K);
    let ntt = AdditiveNttF64::standard(LOG_K + 1);
    let mut codewords = vec![0; 2 * payload.len()];
    // One blob at a time: each transform dispatches to the thread pool itself.
    for (codeword, blob) in codewords
        .as_chunks_mut::<M>()
        .0
        .iter_mut()
        .zip(payload.as_chunks::<{ M / 2 }>().0)
    {
        // The blob's evaluations to its coefficients, in the novel basis.
        codeword[..M / 2].copy_from_slice(blob);
        let codeword = as_field(codeword);
        interpolation.inverse_transform(&mut codeword[..M / 2]);
        // The coefficients to evaluations on a domain twice as large: rate 1/2.
        ntt.encode_interleaved_in_place(codeword, 1, 1);
    }
    codewords
}

/// `L`: the codeword of the tensor `(1, z_0) x .. x (1, z_13)`, each `z_j` drawn from the root.
///
/// It spans every novel-basis coefficient below `k`, so it is a codeword.
///
/// The code is self-dual at rate 1/2, so `L` is orthogonal to every codeword.
fn dual_codeword(root: &Hash) -> Vec<Dual> {
    // The challenges: the root's two halves observed, then 14 samples in `GF(2^192)`.
    let root: [u8; 32] = std::array::from_fn(|i| (root[i / 8] >> (8 * (i % 8))) as u8);
    // The scheme's own chain, from `BLAKE2s(LABEL)`: one compression per absorbed scalar and per sample.
    let mut cv = digest_words(&primitives::hash::hash(LABEL));
    for x in hash_to_scalars(&root) {
        cv = compress(
            cv,
            [
                F64::new(x.coefficients()[0].to_bits()),
                F64::new(x.coefficients()[1].to_bits()),
                F64::new(x.coefficients()[2].to_bits()),
                DS_OBSERVE,
            ],
        );
    }
    let z: [F192; LOG_K] = std::array::from_fn(|_| {
        cv = compress(cv, [F64::ZERO, F64::ZERO, F64::ZERO, DS_SQUEEZE]);
        F192::new([
            F64::new(cv[0].to_bits()),
            F64::new(cv[1].to_bits()),
            F64::new(cv[2].to_bits()),
        ])
    });

    // The tensor, built by doubling: after step `j` its first `2^(j+1)` entries are set.
    //
    //     [1]  ->  [1, z_0]  ->  [1, z_0, z_1, z_0 z_1]  ->  ..
    let mut tensor = vec![F192::ZERO; M];
    tensor[0] = F192::ONE;
    for (j, &zj) in z.iter().enumerate() {
        let (low, high) = tensor[..2 << j].split_at_mut(1 << j);
        for (h, &l) in high.iter_mut().zip(low.iter()) {
            *h = l * zj;
        }
    }
    // The NTT is K-linear, so an F192 codeword is three K-codewords, one per limb.
    let mut limbs: Vec<u64> = tensor
        .iter()
        .flat_map(|t| {
            [
                t.coefficients()[0].to_bits(),
                t.coefficients()[1].to_bits(),
                t.coefficients()[2].to_bits(),
            ]
        })
        .collect();
    AdditiveNttF64::standard(LOG_K + 1).encode_interleaved_in_place(as_field(&mut limbs), 3, 1);
    limbs.as_chunks::<3>().0.to_vec()
}

/// Symbols as the field elements they are, in place.
const fn as_field(words: &mut [u64]) -> &mut [F64] {
    // SAFETY: `F64` is `repr(transparent)` over `u64`, every bit pattern valid.
    unsafe { core::slice::from_raw_parts_mut(words.as_mut_ptr().cast(), words.len()) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanda::{DaError, Hash};
    use leanvm_core::{Machine, Program, Trap};
    use primitives::PrimeCharacteristicRing;

    fn hex(words: &[u64]) -> String {
        words
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    #[test]
    fn leanda_is_the_specified_scheme() {
        // Known answers of the leanDA reference implementation: the root and `H(L)`.
        //
        // Fixture state: 3 blobs, padded to 4 rows, so the padding digests are covered too.
        let codewords = encode(&payload(3));
        let mut cells = vec![[[0; 4]; CELLS]; 4];
        let root = leanda::commit(codewords.as_chunks::<M>().0, &mut cells).unwrap();
        let dual = dual_codeword(&root);
        assert_eq!(
            hex(&root),
            "dcb553cafc216cbb85fa63840f171bca8638fc1be264c99fe96a50af23c4693f"
        );
        assert_eq!(
            hex(&leanda::dual_digest(dual.as_slice().try_into().unwrap())),
            "8356c17fff51207a0a30bca1089c12aefb09546e4d77d4f7c7a5be6c05425f3c"
        );
    }

    #[test]
    fn the_membership_check_is_the_field_inner_product() {
        // Invariant: the guest's inner product is the field's, for any row and dual.
        //
        // So the test uses no codeword at all, only the host's field arithmetic.
        let mut state = 0x243F_6A88_85A3_08D3u64;
        let mut next = || {
            // SplitMix64.
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let z = (state ^ (state >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        let mut cells = vec![[[0; 4]; CELLS]; 1];
        for _ in 0..2 {
            // Fixture state: a random row, odd symbols so `w_0` is invertible, and a random dual.
            let row: Vec<u64> = (0..M).map(|_| next() | 1).collect();
            let mut dual: Vec<Dual> = (0..M).map(|_| [next(), next(), next()]).collect();
            // Solve for `L_0`, limb by limb, so that the inner product is zero:
            //
            //     L_0 w_0 + sum_{x >= 1} L_x w_x = 0   =>   L_0 = (sum_{x >= 1} L_x w_x) / w_0
            let (first, tail) = dual.split_first_mut().unwrap();
            for (c, limb) in first.iter_mut().enumerate() {
                let rest = tail.iter().zip(&row[1..]).fold(F64::ZERO, |acc, (dual, &value)| {
                    acc + F64::new(dual[c]) * F64::new(value)
                });
                *limb = (rest * F64::new(row[0]).invert_or_zero()).to_bits();
            }
            let row: &[[u64; M]] = &[row.try_into().unwrap()];
            let check = |dual: &[Dual], cells: &mut [[Hash; CELLS]]| {
                leanda::check(dual.try_into().unwrap(), row, cells).map(|_| ())
            };
            assert_eq!(check(&dual, &mut cells), Ok(()));

            // Mutation: one bit of `L_0`, which moves the product by `t^bit * w_0 != 0`.
            //
            //     limb 0 bit 0    the lowest bit
            //     limb 1 bit 11   a middle bit
            //     limb 2 bit 55   a bit whose product reaches past x^63
            //     limb 0 bit 63   the top bit, whose product reaches degree 126
            for (c, bit) in [(0, 0), (1, 11), (2, 55), (0, 63)] {
                let mut broken = dual.clone();
                broken[0][c] ^= 1 << bit;
                assert_eq!(
                    check(&broken, &mut cells),
                    Err(DaError::NotACodeword { row: 0 }),
                    "limb {c} bit {bit}"
                );
            }
        }
    }

    /// The guest on the interpreter, with no proof: its output, or the trap.
    fn on_the_vm(run: &Run) -> Result<[u64; 4], Trap> {
        let program = Program::from_elf(ELF).expect("the guest's ELF file");
        Machine::new(program.rv(), &run.advice).run()
    }

    #[test]
    fn the_guest_checks_what_the_native_code_checks() {
        // The guest on the interpreter outputs what its code computes natively.
        let mut run = blobs(1);
        assert_eq!(on_the_vm(&run), Ok(run.expected));

        // Mutation: the top bit of the last parity symbol, which no row digest covers.
        //
        //     only the membership check can see it → the guest panics → no output
        *run.advice.last_mut().unwrap() ^= 1 << 63;
        assert!(on_the_vm(&run).is_err());
    }
}
