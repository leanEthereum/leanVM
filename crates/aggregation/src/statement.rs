//! Claim-list digests and a node's public statement.

use super::AggregateClaims;
use super::cells::{cell_bytes, count, pack_16_bytes};
use super::deferred::DeferredBytecodeClaim;
use super::guest::fs_seed;
use fiat_shamir_prover::merkle::hash_to_scalars;
use primitives::field::F128;

/// Claims the guest hashes a loop frame: 68 cells, four whole block pairs.
pub(super) const CLAIM_GROUP: usize = 17;
const _: () = assert!((CLAIM_GROUP * 64).is_multiple_of(2 * keccak256::RATE));
/// Groups of [`CLAIM_GROUP`] the guest's main list loop hashes a frame.
pub(super) const BIG_GROUPS: usize = 8;
const CLAIM_BIG: usize = CLAIM_GROUP * BIG_GROUPS;

/// How the guest splits a list of `n` claims: the whole frames of [`CLAIM_BIG`], then
/// the whole groups of [`CLAIM_GROUP`], then the claims after them. Its own product
/// identity and range checks pin all three, so this only has to agree with them
/// (`list_split` in the guest). A list is never empty here: both claim lists are
/// guarded at the call, since the guest hashes an empty one without a split at all.
pub(super) fn list_split(n: usize) -> Vec<F128> {
    assert!(n > 0, "an empty list has no split");
    let rest = n % CLAIM_BIG;
    vec![
        count(n / CLAIM_BIG),
        count(rest / CLAIM_GROUP),
        count(rest % CLAIM_GROUP),
    ]
}

/// A claim of either scheme: its pubkey's bytes (`to_bytes`), then the message. Both pubkeys derive `Ord` over their
/// two 16-byte fields in `to_bytes` order, so claims sort as these bytes do.
pub(super) type Claim = [[u8; 32]; 2];

/// Both lists of `claims`, leanXMSS then leanSPHINCS.
#[inline(never)]
pub(super) fn claim_lists(claims: &AggregateClaims) -> [Vec<Claim>; 2] {
    [
        claims
            .lean_xmss
            .iter()
            .map(|(pk, message)| [pk.to_bytes(), *message])
            .collect(),
        claims
            .lean_sphincs
            .iter()
            .map(|(pk, message)| [pk.to_bytes(), *message])
            .collect(),
    ]
}

/// One scheme's declared claims, hashed plainly: 64 bytes a claim, and an empty list hashes the empty string. The
/// guest computes this same digest [`CLAIM_GROUP`] claims at a time (`claim_list_digest`).
pub(super) fn claim_list_digest(claims: &[Claim]) -> [F128; 2] {
    hash_to_scalars(&keccak256::hash(claims.as_flattened().as_flattened()))
}

/// A claim as the four cells the guest hashes and its verifier reads, each 16 bytes little-endian.
pub(super) fn claim_cells([pk, message]: &Claim) -> Vec<F128> {
    vec![
        pack_16_bytes(pk),
        pack_16_bytes(&pk[16..]),
        pack_16_bytes(message),
        pack_16_bytes(&message[16..]),
    ]
}

/// The statement's fixed header, ahead of the deferred cells: the seed, the two
/// claim-list digests (leanXMSS then leanSPHINCS), and the DA digest ([`verifier::da::digest`]).
/// Fed to the guest as `STMT_HEADER`, which pins where its deferred cells start;
/// the header cells themselves are written out again there, and only the
/// end-to-end statement check holds the two spellings together.
pub(super) const STATEMENT_HEADER: usize = 8;

/// A node's public statement, hashed to the two words the VM publishes as its public input. The
/// guest's `statement_digest` computes exactly this, both for itself and when it
/// rebuilds a child's, which is what forces a whole tree onto one bytecode and
/// each child's claims, bound by the two list digests, onto its parent's lists.
///
/// Fixed-length preimage, so a plain hash, with no domain tag of its own: every
/// field has a fixed width, and the header leads with the environment digest, which
/// binds this bytecode and the proof system's version and so already separates the
/// preimage from every other use of the hash here. The header cells, then the
/// deferred cells, each hashed as its two lanes (the guest's `keccak_cells`). Each
/// claim list's digest binds its own length through the hash's padding, so the
/// pair binds both lists whole.
pub(super) fn statement_digest(
    lists: &[Vec<Claim>; 2],
    da_commitment: Option<[u8; 32]>,
    defer: &DeferredBytecodeClaim,
) -> [F128; 2] {
    let header: [[F128; 2]; STATEMENT_HEADER / 2] = [
        fs_seed(),
        claim_list_digest(&lists[0]),
        claim_list_digest(&lists[1]),
        hash_to_scalars(&verifier::da::digest(da_commitment)),
    ];
    let cells = header.as_flattened().iter().copied().chain(defer.cells());
    hash_to_scalars(&keccak256::hash(&cell_bytes(cells)))
}

#[cfg(test)]
mod tests {
    use super::Claim;
    use lean_sphincs::LeanSphincsPublicKey;
    use lean_xmss::LeanXmssPublicKey;

    /// Both schemes' claims sort as their bytes, which the coverage and the digests sort and hash.
    #[test]
    fn claims_sort_as_their_bytes() {
        let mut claims: Vec<Claim> = Vec::new();
        for i in 0..64 {
            for value in [0, 7, 255] {
                let mut claim = [[7; 32]; 2];
                claim[i / 32][i % 32] = value;
                claims.push(claim);
            }
        }
        let lean_xmss = |[pk, message]: &Claim| (LeanXmssPublicKey::from_bytes(pk), *message);
        let lean_sphincs = |[pk, message]: &Claim| (LeanSphincsPublicKey::from_bytes(pk), *message);
        for a in &claims {
            assert_eq!(lean_xmss(a).0.to_bytes(), a[0]);
            assert_eq!(lean_sphincs(a).0.to_bytes(), a[0]);
            for b in &claims {
                assert_eq!(lean_xmss(a).cmp(&lean_xmss(b)), a.cmp(b));
                assert_eq!(lean_sphincs(a).cmp(&lean_sphincs(b)), a.cmp(b));
            }
        }
    }
}
