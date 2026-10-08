//! The verified transcript-step block against `fiat_shamir::step_block`.
//!
//! The circuit's copy (`builder_step_message`) has no public production counterpart (`Builder` lives in
//! `leanvm_core`'s private `rec` module); it is checked against the native block here, and production's
//! `rec::transcript::tests::the_circuit_replays_the_native_transcript` checks the circuit's steps hash to the
//! native ones.
use leanvm_verus::fiat_shamir as verified;
use leanvm_verus::gf2_64::F64 as VF64;
use leanvm_verus::gf2_64x3::F192 as VF192;
use primitives::field::{F192, F64};
use primitives::test_util::Rng;

fn to_v(e: F192) -> VF192 {
    VF192::new(e.c0, e.c1, e.c2)
}

fn scalars(rng: &mut Rng) -> Vec<F192> {
    let n = (rng.next_u32() % 3) as usize;
    (0..n)
        .map(|_| match rng.next_u32() % 4 {
            0 => F192::ZERO,
            1 => F192::new(u64::MAX, u64::MAX, u64::MAX),
            _ => rng.ext(),
        })
        .collect()
}

#[test]
fn step_blocks_match() {
    let mut rng = Rng::new(0xF5B1);
    let tags = [0, 1, 2, 3, 4, u64::MAX];
    for round in 0..20_000 {
        let s = scalars(&mut rng);
        let tag = if round % 2 == 0 {
            tags[round / 2 % tags.len()]
        } else {
            rng.next_u64()
        };
        let want = fiat_shamir::step_block(&s, F64(tag)).map(|w| w.0);
        let vs: Vec<VF192> = s.iter().copied().map(to_v).collect();
        assert_eq!(
            verified::step_block(&vs, VF64(tag)).map(|w| w.0),
            want,
            "{s:?} {tag:#x}"
        );
        assert_eq!(verified::builder_step_message(&vs, tag), want, "{s:?} {tag:#x}");
    }
}

#[test]
fn constants_match() {
    assert_eq!(verified::MAX_PENDING, fiat_shamir::MAX_PENDING);
    assert_eq!(verified::DS_OBSERVE.0, fiat_shamir::DS_OBSERVE.0);
    assert_eq!(verified::DS_SQUEEZE.0, fiat_shamir::DS_SQUEEZE.0);
    assert_eq!(verified::DS_POW_BASE.0, fiat_shamir::DS_POW_BASE.0);
    assert_eq!(verified::DS_POW_NONCE.0, fiat_shamir::DS_POW_NONCE.0);
}
