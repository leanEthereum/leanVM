//! Length dispatch and pubkey pairing.
//!
//! `proof_or_sig` deliberately mixes raw XMSS signatures with previously produced aggregates,
//! so a caller can fold an existing aggregate together with fresh signatures. This module
//! splits that vector back apart.

use crate::Error;
use rec_aggregation::SingleMessageAggregateSignature;
use ssz::Decode;
use xmss::{SIGNATURE_SSZ_LEN, XmssPublicKey, XmssSignature};

/// A raw signature paired with the public key that produced it.
type Raw = (XmssPublicKey, XmssSignature);

/// A raw XMSS signature is exactly `SIGNATURE_SSZ_LEN` bytes; anything else is parsed as an
/// aggregate. Counted once and dispatched on once, so the two cannot drift apart.
///
/// Drift here would be silent and severe: a predicate that counts more entries than the loop
/// classifies as signatures leaves `signatures` shorter than `pubkeys`, and the `zip` below
/// then truncates and pairs every later signature with the wrong key — a valid proof of the
/// wrong signer set, with no decode error to show for it.
const fn is_raw_signature(entry: &[u8]) -> bool {
    entry.len() == SIGNATURE_SSZ_LEN
}

/// Splits the mixed input vector into raw signatures (paired with their pubkeys) and
/// previously produced aggregates.
///
/// Entries are classified by length: exactly `SIGNATURE_SSZ_LEN` means a raw signature,
/// anything else is parsed as a postcard aggregate. A correctly sized blob that fails SSZ
/// decode is `MalformedSignature`, never a fallback to the aggregate parser — silent
/// reclassification would surface as a baffling failure much later.
///
/// Aggregates carry their own signer sets, so `public_keys` covers raw signatures only:
/// the k-th raw entry pairs with `public_keys[k]`. The two vectors are therefore *not*
/// index-aligned whenever an aggregate is present.
///
/// An empty `proof_or_sig` is `Error::Empty`. The check lives here rather than in the caller
/// because this module owns the input vector, and the planner downstream documents that it
/// expects the empty case to have been rejected already.
///
/// The index-carrying errors point into *different* vectors, each named by its variant:
/// `MalformedEntry { index }` and `MalformedSignature { index }` index `proof_or_sig`,
/// `MalformedPublicKey { index }` indexes `public_keys`. Reporting a pubkey fault against a
/// `proof_or_sig` position would point the caller at a blob it cannot fix. The two entry
/// faults are kept apart because their remedies differ: a signature-sized blob that fails to
/// decode is damaged data, not data of the wrong kind.
///
/// Every public key is decoded before any entry is, so when both vectors hold a bad blob the
/// public key is reported whatever the two positions are. That is a stable rule rather than
/// one that shifts with how the two vectors interleave, and it is pinned by test — changing
/// it is therefore a deliberate act rather than a side effect.
///
/// Both arguments are taken by value and consumed as they are decoded, so the caller's byte
/// buffers (up to tens of megabytes at the signer ceiling) are freed here rather than living
/// on through all the proving that follows.
///
/// This cannot panic. In particular `SingleMessageAggregateSignature::from_bytes` returns
/// `None` rather than panicking when the aggregation bytecode is uninitialized, which would
/// surface here as `MalformedEntry`; every public entry point calls
/// `init_aggregation_bytecode()` first so that cannot happen.
pub(crate) fn classify(
    proof_or_sig: Vec<Vec<u8>>,
    public_keys: Vec<Vec<u8>>,
) -> Result<(Vec<Raw>, Vec<SingleMessageAggregateSignature>), Error> {
    if proof_or_sig.is_empty() {
        return Err(Error::Empty);
    }

    let expected = proof_or_sig.iter().filter(|e| is_raw_signature(e.as_slice())).count();
    if expected != public_keys.len() {
        return Err(Error::PubkeyCountMismatch {
            expected,
            got: public_keys.len(),
        });
    }

    // `from_ssz_bytes` enforces the fixed length itself, so a short or long blob and one
    // holding non-canonical field elements both land on the same variant.
    let pubkeys = public_keys
        .into_iter()
        .enumerate()
        .map(|(index, bytes)| XmssPublicKey::from_ssz_bytes(&bytes).map_err(|_| Error::MalformedPublicKey { index }))
        .collect::<Result<Vec<_>, _>>()?;

    let mut signatures = Vec::with_capacity(expected);
    let mut aggregates = Vec::new();

    for (index, entry) in proof_or_sig.into_iter().enumerate() {
        if is_raw_signature(&entry) {
            signatures.push(XmssSignature::from_ssz_bytes(&entry).map_err(|_| Error::MalformedSignature { index })?);
        } else {
            aggregates
                .push(SingleMessageAggregateSignature::from_bytes(&entry).ok_or(Error::MalformedEntry { index })?);
        }
    }

    // `zip` would silently truncate on a length mismatch; the count check above is what makes
    // it exact, and it counted `is_raw_signature` — the same function this loop dispatches on.
    debug_assert_eq!(pubkeys.len(), signatures.len());
    Ok((pubkeys.into_iter().zip(signatures).collect(), aggregates))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ssz::Encode;
    use xmss::{xmss_key_gen_from_seed, xmss_sign};

    fn sample(seed: u8) -> (Vec<u8>, Vec<u8>) {
        let (pk, sk) = xmss_key_gen_from_seed([seed; 32], 100, 16).unwrap();
        let sig = xmss_sign(&sk, 100, &[7u8; 32]).unwrap();
        (pk.as_ssz_bytes(), sig.as_ssz_bytes())
    }

    #[test]
    fn classifies_raw_signatures_by_length() {
        let (pk, sig) = sample(1);
        assert_eq!(sig.len(), xmss::SIGNATURE_SSZ_LEN);
        let (raw, aggs) = classify(vec![sig], vec![pk]).unwrap();
        assert_eq!(raw.len(), 1);
        assert!(aggs.is_empty());
    }

    #[test]
    fn rejects_a_correctly_sized_but_corrupt_signature() {
        // A 1208-byte blob that fails SSZ decode is an error rather than a success. This
        // cannot show that it was not first tried as an aggregate: that path also returns
        // `None` with no bytecode initialized, so a fall-through classifier would produce an
        // error here too. Fall-through is ruled out by the if/else in `classify`, not by this.
        let (pk, mut sig) = sample(2);
        sig[0] = 0xff;
        sig[1] = 0xff;
        sig[2] = 0xff;
        sig[3] = 0xff; // non-canonical field element
        assert!(matches!(
            classify(vec![sig], vec![pk]),
            Err(Error::MalformedSignature { index: 0 })
        ));
    }

    #[test]
    fn pubkey_count_must_match_raw_count() {
        let (pk, sig) = sample(3);
        let err = classify(vec![sig.clone(), sig], vec![pk]).unwrap_err();
        assert!(matches!(err, Error::PubkeyCountMismatch { expected: 2, got: 1 }));
    }

    #[test]
    fn rejects_a_wrong_length_pubkey() {
        let (_, sig) = sample(4);
        assert!(matches!(
            classify(vec![sig], vec![vec![0u8; 8]]),
            Err(Error::MalformedPublicKey { index: 0 })
        ));
    }

    #[test]
    fn rejects_a_right_length_but_non_canonical_pubkey() {
        // The other half of what `from_ssz_bytes` covers, and the reason no explicit length
        // pre-check is needed here: 0xffffffff exceeds the KoalaBear modulus, so a correctly
        // sized blob is still rejected. If canonicality checking is ever lost upstream, this
        // is what catches it.
        let (_, sig) = sample(9);
        assert!(matches!(
            classify(vec![sig], vec![vec![0xffu8; xmss::PUB_KEY_SSZ_LEN]]),
            Err(Error::MalformedPublicKey { index: 0 })
        ));
    }

    #[test]
    fn reports_a_malformed_pubkey_ahead_of_a_malformed_signature() {
        // Documented ordering: all pubkeys decode before any entry, so the pubkey wins even
        // though the corrupt entry sits at a lower position in its own vector.
        let (pk, mut sig) = sample(10);
        sig[0] = 0xff;
        sig[1] = 0xff;
        sig[2] = 0xff;
        sig[3] = 0xff;
        assert!(matches!(
            classify(vec![sig.clone(), sig], vec![pk, vec![0xffu8; xmss::PUB_KEY_SSZ_LEN]]),
            Err(Error::MalformedPublicKey { index: 1 })
        ));
    }

    #[test]
    fn pairs_each_pubkey_with_its_own_signature() {
        // Counts alone would pass a reversed or off-by-one pairing, which verifies as a proof
        // of the wrong signer set rather than as a decode failure.
        let (pk_a, sig_a) = sample(5);
        let (pk_b, sig_b) = sample(6);
        assert_ne!(pk_a, pk_b);
        let (raw, _) = classify(vec![sig_a.clone(), sig_b.clone()], vec![pk_a.clone(), pk_b.clone()]).unwrap();
        let expected: Vec<Raw> = [(pk_a, sig_a), (pk_b, sig_b)]
            .into_iter()
            .map(|(pk, sig)| {
                (
                    XmssPublicKey::from_ssz_bytes(&pk).unwrap(),
                    XmssSignature::from_ssz_bytes(&sig).unwrap(),
                )
            })
            .collect();
        assert_eq!(raw, expected);
    }

    #[test]
    fn too_many_pubkeys_is_rejected() {
        // The misuse the module doc predicts: a caller assuming the two vectors ARE
        // index-aligned supplies one pubkey per entry, aggregates included.
        let (pk_a, sig) = sample(11);
        let (pk_b, _) = sample(12);
        assert!(matches!(
            classify(vec![sig, vec![0u8; 9]], vec![pk_a, pk_b]),
            Err(Error::PubkeyCountMismatch { expected: 1, got: 2 })
        ));
    }

    #[test]
    fn a_non_signature_entry_does_not_consume_a_pubkey() {
        // The asymmetry this module exists for: an aggregate carries its own signer set, so
        // only raw entries count towards `public_keys.len()`. One raw entry here, so one
        // pubkey is expected however many non-raw entries sit beside it.
        let (_, sig) = sample(7);
        assert!(matches!(
            classify(vec![vec![0u8; 9], sig], vec![]),
            Err(Error::PubkeyCountMismatch { expected: 1, got: 0 })
        ));
    }

    #[test]
    fn an_unparseable_non_signature_entry_reports_its_index_in_proof_or_sig() {
        // Coverage of the aggregate branch stops here: this only shows that a blob which is no
        // aggregate is rejected against its own `proof_or_sig` position (1, not 0, which is
        // where it lands among the aggregates). Parsing a *real* aggregate needs a real prover
        // and `init_aggregation_bytecode`; that is the integration tests' job.
        let (pk, sig) = sample(8);
        assert!(matches!(
            classify(vec![sig, vec![0u8; 9]], vec![pk]),
            Err(Error::MalformedEntry { index: 1 })
        ));
    }

    #[test]
    fn empty_input_is_rejected() {
        assert!(matches!(classify(vec![], vec![]), Err(Error::Empty)));
    }
}
