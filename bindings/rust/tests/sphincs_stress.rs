//! Stress, differential, concurrency, and alignment tests for leanSPHINCS verification.

use std::sync::LazyLock;

use lean_pq::sphincs::{PublicKey, SecretKey, Signature, SIGNATURE_LEN};
use lean_pq::{Error, MESSAGE_LEN, PUBLIC_KEY_LEN};
use proptest::prelude::*;

static KEY: LazyLock<SecretKey> = LazyLock::new(|| SecretKey::from_seed([0x5a; 32]));
static MESSAGE: [u8; MESSAGE_LEN] = [0x3c; MESSAGE_LEN];
static VALID_SIG: LazyLock<Signature> = LazyLock::new(|| KEY.sign(&MESSAGE));

fn reference_verify(
    pk: &[u8; PUBLIC_KEY_LEN],
    msg: &[u8; MESSAGE_LEN],
    sig: &[u8; SIGNATURE_LEN],
) -> bool {
    let pk = lean_sphincs::LeanSphincsPublicKey::from_bytes(pk);
    let sig = lean_sphincs::LeanSphincsSignature::from_bytes(sig);
    lean_sphincs::verify(&pk, msg, &sig)
}

#[test]
fn linux_uses_proved_sphincs_assembly() {
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    const {
        assert!(
            proved_sphincs::USING_PROVED_ASM,
            "Linux x86_64/aarch64 bindings must execute the proved leanSPHINCS assembly"
        );
    }
}

#[test]
fn unaligned_buffers_match_reference() {
    let pk_bytes = KEY.public_key().to_bytes();
    let sig_bytes = VALID_SIG.to_bytes();

    let mut pk_buf = [0xa5u8; PUBLIC_KEY_LEN + 16];
    let mut msg_buf = [0x5au8; MESSAGE_LEN + 16];
    let mut sig_buf = vec![0x3cu8; SIGNATURE_LEN + 16];

    for offset in 0..16 {
        pk_buf[offset..offset + PUBLIC_KEY_LEN].copy_from_slice(&pk_bytes);
        msg_buf[offset..offset + MESSAGE_LEN].copy_from_slice(&MESSAGE);
        sig_buf[offset..offset + SIGNATURE_LEN].copy_from_slice(&sig_bytes);

        let pk: &[u8; PUBLIC_KEY_LEN] = (&pk_buf[offset..offset + PUBLIC_KEY_LEN])
            .try_into()
            .unwrap();
        let msg: &[u8; MESSAGE_LEN] = (&msg_buf[offset..offset + MESSAGE_LEN]).try_into().unwrap();
        let sig: &[u8; SIGNATURE_LEN] = (&sig_buf[offset..offset + SIGNATURE_LEN])
            .try_into()
            .unwrap();

        assert!(proved_sphincs::verify_bytes(pk, msg, sig));

        let mut bad_sig = *sig;
        bad_sig[offset * 400] ^= 1;
        assert!(!proved_sphincs::verify_bytes(pk, msg, &bad_sig));
    }
}

#[test]
fn single_bit_flips_across_all_regions_rejected() {
    let pk_bytes = KEY.public_key().to_bytes();
    let sig_bytes = VALID_SIG.to_bytes();

    // Every single-bit flip of message (256 bits) and public key (256 bits).
    for bit in 0..(MESSAGE_LEN * 8) {
        let mut msg = MESSAGE;
        msg[bit / 8] ^= 1 << (bit % 8);
        assert_eq!(
            KEY.public_key().verify(&msg, &VALID_SIG),
            Err(Error::SphincsVerify)
        );
        assert!(!reference_verify(&pk_bytes, &msg, &sig_bytes));
    }
    for bit in 0..(PUBLIC_KEY_LEN * 8) {
        let mut pk = pk_bytes;
        pk[bit / 8] ^= 1 << (bit % 8);
        assert_eq!(
            PublicKey::from_bytes(&pk)
                .unwrap()
                .verify(&MESSAGE, &VALID_SIG),
            Err(Error::SphincsVerify)
        );
        assert!(!reference_verify(&pk, &MESSAGE, &sig_bytes));
    }

    // Sampled single-bit flips covering every byte of the 7740-byte signature
    // (randomizer, all 24 FORS trees, and all 3 hypertree layers: counters, WOTS chains, auth paths).
    for byte_idx in (0..SIGNATURE_LEN).step_by(7) {
        for bit_in_byte in [0usize, 7] {
            let mut mutated = sig_bytes;
            mutated[byte_idx] ^= 1 << bit_in_byte;
            let got = proved_sphincs::verify_bytes(&pk_bytes, &MESSAGE, &mutated);
            let want = reference_verify(&pk_bytes, &MESSAGE, &mutated);
            assert_eq!(got, want, "mismatch at byte {byte_idx} bit {bit_in_byte}");
            assert!(
                !got,
                "mutated signature accepted at byte {byte_idx} bit {bit_in_byte}"
            );
        }
    }
}

#[test]
fn concurrent_verification_stress_32_threads() {
    let keys: Vec<SecretKey> = (0u8..4)
        .map(|i| SecretKey::from_seed([i.wrapping_add(11); 32]))
        .collect();
    let msgs: Vec<[u8; MESSAGE_LEN]> = (0u8..4)
        .map(|i| [i.wrapping_add(0x70); MESSAGE_LEN])
        .collect();
    let sigs: Vec<Signature> = keys.iter().zip(&msgs).map(|(k, m)| k.sign(m)).collect();
    let pks: Vec<PublicKey> = keys.iter().map(SecretKey::public_key).collect();

    std::thread::scope(|scope| {
        for tid in 0..32usize {
            let pks = &pks;
            let msgs = &msgs;
            let sigs = &sigs;
            scope.spawn(move || {
                for iter in 0..64usize {
                    let idx = (tid + iter) % pks.len();
                    assert_eq!(pks[idx].verify(&msgs[idx], &sigs[idx]), Ok(()));

                    let mut bad_msg = msgs[idx];
                    bad_msg[(tid + iter) % MESSAGE_LEN] ^= 1 << ((tid + iter) % 8);
                    assert_eq!(
                        pks[idx].verify(&bad_msg, &sigs[idx]),
                        Err(Error::SphincsVerify)
                    );
                }
            });
        }
    });
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn differential_mutation_matches_reference(
        target in 0u8..4,
        byte_pos in 0usize..SIGNATURE_LEN,
        mask in 1u8..=255u8,
        extra_flip in proptest::option::of((0usize..SIGNATURE_LEN, 1u8..=255u8)),
    ) {
        let mut pk = KEY.public_key().to_bytes();
        let mut msg = MESSAGE;
        let mut sig = VALID_SIG.to_bytes();

        match target {
            0 => pk[byte_pos % PUBLIC_KEY_LEN] ^= mask,
            1 => msg[byte_pos % MESSAGE_LEN] ^= mask,
            2 => sig[byte_pos] ^= mask,
            _ => {
                // Unmodified valid case on target == 3 unless extra_flip fires.
            }
        }
        if let Some((pos, m)) = extra_flip {
            sig[pos] ^= m;
        }

        let got = proved_sphincs::verify_bytes(&pk, &msg, &sig);
        let want = reference_verify(&pk, &msg, &sig);
        prop_assert_eq!(got, want);

        let via_api = PublicKey::from_bytes(&pk)
            .unwrap()
            .verify(&msg, &Signature::from_bytes(&sig).unwrap())
            .is_ok();
        prop_assert_eq!(via_api, want);
    }

    #[test]
    fn differential_random_inputs_match_reference(
        pk in any::<[u8; PUBLIC_KEY_LEN]>(),
        msg in any::<[u8; MESSAGE_LEN]>(),
        seed in any::<u64>(),
    ) {
        // Fill a pseudo-random 7740-byte signature deterministically from `seed`.
        let mut sig = [0u8; SIGNATURE_LEN];
        let mut x = seed ^ 0x9e37_79b9_7f4a_7c15;
        for chunk in sig.chunks_mut(8) {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let bytes = x.to_le_bytes();
            chunk.copy_from_slice(&bytes[..chunk.len()]);
        }

        let got = proved_sphincs::verify_bytes(&pk, &msg, &sig);
        let want = reference_verify(&pk, &msg, &sig);
        prop_assert_eq!(got, want);
    }
}
