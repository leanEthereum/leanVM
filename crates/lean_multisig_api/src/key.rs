//! The `SecretKey` handle.
//!
//! Every other value crossing this crate's boundary is a `Vec<u8>`. This one is not, and that
//! asymmetry is the whole point of the module: see the type's own documentation.

use crate::Error;
use ssz::Encode;
use std::ops::RangeInclusive;
use xmss::{XmssKeyGenError, XmssSecretKey, xmss_key_gen, xmss_key_gen_from_seed, xmss_sign};

// The constructors' `# Errors` docs claim that the lifetime half of `InvalidRange` is
// unreachable through this API: slots are `u32`, so the widest possible range ends at exactly
// `1 << 32`, and upstream only rejects `activation_end > 1 << LOG_LIFETIME`. That claim holds
// only while the lifetime is at least 32 bits, and `LOG_LIFETIME` belongs to another crate.
// Shrinking it upstream makes the documented error reachable and the doc wrong, so fail here
// rather than in a caller's error handling.
const _: () = assert!(xmss::LOG_LIFETIME >= 32);

/// Converts an inclusive slot range into the `(activation_slot, num_active_slots)` pair that
/// `xmss` takes.
///
/// The count is widened to `u64` before the `+ 1`: a full `0..=u32::MAX` range spans 2^32 slots,
/// one more than a `u32` can hold, which is why upstream takes `u64` at all.
///
/// The emptiness check is not a nicety — `end - start` underflows on an inverted range, which
/// panics in debug and silently produces an enormous count in release.
fn span(slots: &RangeInclusive<u32>) -> Result<(u64, u64), Error> {
    let (start, end) = (*slots.start(), *slots.end());
    if start > end {
        // An empty range means zero active slots, which is exactly the condition upstream
        // already rejects as `InvalidRange`. Reusing it keeps one meaning for one fault
        // rather than giving the caller two names to match on for the same mistake.
        return Err(Error::KeyGen(XmssKeyGenError::InvalidRange));
    }
    Ok((u64::from(start), u64::from(end - start) + 1))
}

/// An XMSS secret key, active for a fixed slot range.
///
/// This is a handle rather than a byte slice on purpose. [`XmssSecretKey`] holds a
/// bottom-subtree cache that [`sign`](Self::sign) warms and reuses across calls, and
/// serialization deliberately drops that cache. A bytes-in/bytes-out `sign` would therefore
/// deserialize the top tree and rebuild a bottom subtree on *every* signature. Bytes appear
/// here only at the boundary, via [`to_bytes`](Self::to_bytes) and
/// [`from_bytes`](Self::from_bytes), where they are genuinely a storage format.
///
/// # Warning: XMSS is stateful
///
/// Never sign two different messages at the same slot; doing so leaks the one-time WOTS key
/// for that slot. Signing is derandomized from `(seed, slot, message)`, so repeating the same
/// `(slot, message)` is harmless and returns identical bytes. This type does *not* track which
/// slots have been used — that state belongs to the caller, who alone knows what has been
/// published.
///
/// [`to_bytes`](Self::to_bytes)/[`from_bytes`](Self::from_bytes) carry no usage state either:
/// restoring the same bytes twice yields two keys that know nothing about each other or about
/// what the original signed. A caller must persist its own high-water slot alongside the key
/// bytes, advance and durably store it *before* publishing a signature, and never sign at or
/// below it with different content.
///
/// # Concurrency
///
/// The cache sits behind a mutex, so the type is `Send + Sync` and [`sign`](Self::sign) takes
/// `&self`. Concurrent signing is therefore sound, but not fast: the cache holds exactly one
/// bottom subtree, so threads signing slots that fall in *different* subtrees evict each
/// other's entry and rebuild it, on top of serializing on the mutex. Sign sequentially per
/// key, or give each concurrent signer its own key.
///
/// # Secrecy
///
/// The derived [`Debug`] delegates to `XmssSecretKey`'s hand-written one, which prints only the
/// slot range and split level and is `finish_non_exhaustive`. Neither the seed nor the tree is
/// printed, so logging a `SecretKey` does not leak key material. This is pinned by a test.
#[derive(Debug)]
pub struct SecretKey(XmssSecretKey);

impl SecretKey {
    /// Generates a key active for exactly `slots`, seeded from the operating system.
    ///
    /// The range is inclusive at both ends and round-trips through [`slots`](Self::slots):
    /// `SecretKey::generate(100..=115)?.slots() == 100..=115`.
    ///
    /// Keygen cost is linear in the width of the range, so a wide range is not free — it builds
    /// one Merkle leaf per slot.
    ///
    /// # Errors
    ///
    /// [`Error::KeyGen`] if `slots` is empty, meaning `end < start`. The variant also covers a
    /// range extending past the XMSS lifetime, which no `u32` range can do while `LOG_LIFETIME`
    /// is 32: `0..=u32::MAX` lands exactly on the limit, guaranteed by a compile-time assertion
    /// in this module.
    ///
    /// # Panics
    ///
    /// If the OS entropy source is unavailable, which `rand`'s thread RNG treats as fatal.
    pub fn generate(slots: RangeInclusive<u32>) -> Result<Self, Error> {
        let (activation_slot, num_active_slots) = span(&slots)?;
        let mut rng = rand::rng();
        let (_, sk) = xmss_key_gen(&mut rng, activation_slot, num_active_slots)?;
        Ok(Self(sk))
    }

    /// Deterministic [`Self::generate`]. The seed is the key's entire secret material: the same
    /// `(seed, slots)` always regenerates the same key.
    ///
    /// # Errors
    ///
    /// As [`Self::generate`].
    pub fn from_seed(seed: [u8; 32], slots: RangeInclusive<u32>) -> Result<Self, Error> {
        let (activation_slot, num_active_slots) = span(&slots)?;
        let (_, sk) = xmss_key_gen_from_seed(seed, activation_slot, num_active_slots)?;
        Ok(Self(sk))
    }

    /// Restores a key from [`Self::to_bytes`].
    ///
    /// The signing cache starts empty, so the first [`sign`](Self::sign) after this rebuilds a
    /// bottom subtree; [`prepare`](Self::prepare) can absorb that cost ahead of time.
    ///
    /// Usage state is not restored either — see the type-level warning. A restored key will
    /// happily re-sign a slot the original already used.
    ///
    /// # Errors
    ///
    /// [`Error::MalformedSecretKey`] if the bytes are truncated, damaged, carry an unsupported
    /// format version, describe a tree whose shape contradicts its slot range, or have trailing
    /// bytes after a complete key. Trailing bytes are rejected rather than ignored so that a
    /// key has exactly one encoding.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let (key, rest) = postcard::take_from_bytes::<XmssSecretKey>(bytes).map_err(|_| Error::MalformedSecretKey)?;
        if rest.is_empty() {
            Ok(Self(key))
        } else {
            Err(Error::MalformedSecretKey)
        }
    }

    /// Serializes the key for storage: the seed, slot range, and top tree.
    ///
    /// The bottom-subtree cache is *not* persisted — it is derived state, cheap to rebuild and
    /// meaningless without the slot it was built for.
    ///
    /// The returned bytes are the key's entire secret material: anyone holding them can sign.
    /// Neither this crate nor `xmss` zeroizes anything, so wiping this buffer, and any file it
    /// is written to, is the caller's responsibility.
    ///
    /// # Panics
    ///
    /// Never. `postcard::to_allocvec` grows its output buffer, so the only remaining failure
    /// mode is a `Serialize` impl reporting a custom error, and `XmssSecretKey` serializes as a
    /// tuple of integers, byte arrays, and vectors, none of which can. The same reasoning backs
    /// the identical `expect` in `rec_aggregation`'s aggregate codecs.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.0).expect("XmssSecretKey serialization is infallible")
    }

    /// The matching public key, SSZ-encoded: exactly `xmss::PUB_KEY_SSZ_LEN` bytes, ready to
    /// hand to `aggregate` alongside a signature.
    #[must_use]
    pub fn public_key(&self) -> Vec<u8> {
        self.0.public_key().as_ssz_bytes()
    }

    /// The inclusive range of slots this key can sign for.
    #[must_use]
    pub const fn slots(&self) -> RangeInclusive<u32> {
        self.0.activation_slots()
    }

    /// Warms the signing cache for `slot`.
    ///
    /// Worth calling when the next slot is known ahead of time; this is the one tuning choice
    /// the library cannot make for you, because only the caller knows which slot is coming.
    /// Calling it is never required — [`sign`](Self::sign) warms the cache itself.
    ///
    /// # Errors
    ///
    /// [`Error::Sign`] if `slot` is outside [`slots`](Self::slots).
    pub fn prepare(&self, slot: u32) -> Result<(), Error> {
        self.0.prepare(slot).map_err(Into::into)
    }

    /// Signs a 32-byte message at `slot`, returning `xmss::SIGNATURE_SSZ_LEN` SSZ bytes ready
    /// for `aggregate`.
    ///
    /// Read the type-level warning first: signing two different messages at one slot breaks the
    /// scheme, and nothing here prevents it.
    ///
    /// # Errors
    ///
    /// [`Error::Sign`] if `slot` is outside [`slots`](Self::slots), or if no valid WOTS encoding
    /// was found within the attempt budget.
    pub fn sign(&self, message: &[u8; 32], slot: u32) -> Result<Vec<u8>, Error> {
        Ok(xmss_sign(&self.0, slot, message)?.as_ssz_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ssz::Decode;
    use xmss::{XmssPublicKey, XmssSignature};

    #[test]
    fn sign_then_verify_round_trips() {
        // That `sign` and `public_key` agree is the type's functional contract, and it is the
        // one thing length checks and self-relative comparisons cannot see: a `public_key`
        // returning the wrong tree root, or a `sign` encoding against a slot other than the one
        // asked for, leaves every other test in this module green. `aggregate` consumes
        // both, where a disagreement costs a whole tree of proving before surfacing as something
        // unreadable.
        let sk = SecretKey::from_seed([1u8; 32], 100..=115).unwrap();
        let sig = sk.sign(&[9u8; 32], 100).unwrap();
        assert_eq!(sig.len(), xmss::SIGNATURE_SSZ_LEN);
        assert_eq!(sk.public_key().len(), xmss::PUB_KEY_SSZ_LEN);

        let pk = XmssPublicKey::from_ssz_bytes(&sk.public_key()).unwrap();
        let signature = XmssSignature::from_ssz_bytes(&sig).unwrap();
        assert!(xmss::xmss_verify(&pk, 100, &[9u8; 32], &signature).is_ok());

        // Bound to the exact (slot, message) the caller passed, not merely well-formed.
        assert!(xmss::xmss_verify(&pk, 101, &[9u8; 32], &signature).is_err());
        assert!(xmss::xmss_verify(&pk, 100, &[8u8; 32], &signature).is_err());
    }

    #[test]
    fn from_seed_is_deterministic() {
        let a = SecretKey::from_seed([2u8; 32], 100..=115).unwrap();
        let b = SecretKey::from_seed([2u8; 32], 100..=115).unwrap();
        assert_eq!(a.public_key(), b.public_key());
    }

    #[test]
    fn serialization_preserves_signing() {
        // The cache is dropped on deserialize; signatures must still be identical, since
        // signing is derandomized from (seed, slot, message).
        let sk = SecretKey::from_seed([3u8; 32], 100..=115).unwrap();
        let before = sk.sign(&[4u8; 32], 105).unwrap();
        let restored = SecretKey::from_bytes(&sk.to_bytes()).unwrap();
        assert_eq!(restored.public_key(), sk.public_key());
        assert_eq!(restored.sign(&[4u8; 32], 105).unwrap(), before);

        // The positive half of the "exactly one encoding" claim that justifies `take_from_bytes`.
        // `from_parts` recomputes the derived fields on load, so if that recomputation ever
        // diverged from keygen the round trip would break here while signatures still matched.
        assert_eq!(restored.to_bytes(), sk.to_bytes());
    }

    #[test]
    fn repeated_signing_of_one_slot_is_byte_identical() {
        // The safety carve-out on the stateful-signing warning: repeating the same
        // (slot, message) is harmless *because* it returns identical bytes, which is what makes
        // crash-retry safe. Tested twice on a single handle, so it also pins that a warm cache
        // hit — the path this whole caching design exists for — changes nothing about the output.
        let sk = SecretKey::from_seed([12u8; 32], 100..=115).unwrap();
        let message = [13u8; 32];
        let first = sk.sign(&message, 105).unwrap();
        let second = sk.sign(&message, 105).unwrap();
        assert_eq!(first, second);

        // A different message at the same slot must NOT collide; the carve-out is exact.
        assert_ne!(sk.sign(&[14u8; 32], 105).unwrap(), first);
    }

    #[test]
    fn signing_outside_the_slot_range_fails() {
        let sk = SecretKey::from_seed([5u8; 32], 100..=115).unwrap();
        assert_eq!(sk.slots(), 100..=115);
        assert!(sk.sign(&[0u8; 32], 116).is_err());
        assert!(sk.sign(&[0u8; 32], 99).is_err());
    }

    #[test]
    fn prepare_warms_in_range_and_rejects_out_of_range() {
        // `prepare` is the one tuning decision this facade deliberately leaves to the caller,
        // so it should not be the one method with no coverage. Both paths its rustdoc promises
        // are exercised here; the warming itself is a performance effect and is not asserted.
        let sk = SecretKey::from_seed([8u8; 32], 100..=115).unwrap();
        assert!(sk.prepare(105).is_ok());
        // Idempotent: warming a slot already cached must not start reporting failure.
        assert!(sk.prepare(105).is_ok());
        assert!(matches!(sk.prepare(116), Err(Error::Sign(_))));
        assert!(matches!(sk.prepare(99), Err(Error::Sign(_))));
    }

    #[test]
    fn generate_produces_a_key_over_the_requested_range() {
        // The only test that actually runs `generate`: every other call site stops at `span`'s
        // early return, so `rand::rng()` is never reached at runtime. The `CryptoRng` bound is
        // checked at compile time, but that the call succeeds is a separate claim.
        let sk = SecretKey::generate(0..=15).unwrap();
        assert_eq!(sk.slots(), 0..=15);
        assert_eq!(sk.public_key().len(), xmss::PUB_KEY_SSZ_LEN);
    }

    #[test]
    fn generate_is_randomized() {
        // The one property separating `generate` from `from_seed`. Not flaky: the seed is 32
        // bytes from a CSPRNG, so a collision is a 2^-256 event, far below the rate at which
        // the machine running this test would fail in other ways.
        let a = SecretKey::generate(0..=15).unwrap();
        let b = SecretKey::generate(0..=15).unwrap();
        assert_ne!(a.public_key(), b.public_key());
    }

    #[test]
    fn malformed_bytes_are_rejected() {
        assert!(matches!(
            SecretKey::from_bytes(&[0u8; 3]),
            Err(Error::MalformedSecretKey)
        ));
    }

    #[test]
    fn an_empty_range_is_rejected() {
        // `end - start` underflows on an inverted range: a debug panic, or in release a count
        // near 2^32 that would send keygen away for the rest of the decade. Both constructors
        // must reject it, and both must call it the same thing upstream already does.
        for (start, end) in [(100u32, 99u32), (1, 0), (u32::MAX, 0)] {
            // Built with `RangeInclusive::new` rather than written as `100..=99`, which trips
            // clippy's deny-by-default `reversed_empty_ranges`. That lint only sees literals,
            // so it protects nobody who computes the bounds at runtime — which is precisely the
            // case `span` has to catch, and the reason this test is not redundant with it.
            let slots = RangeInclusive::new(start, end);
            assert!(matches!(
                SecretKey::from_seed([7u8; 32], slots.clone()),
                Err(Error::KeyGen(XmssKeyGenError::InvalidRange))
            ));
            assert!(matches!(
                SecretKey::generate(slots),
                Err(Error::KeyGen(XmssKeyGenError::InvalidRange))
            ));
        }
    }

    #[test]
    fn the_full_slot_range_converts_without_overflowing() {
        // `0..=u32::MAX` spans 2^32 slots, one more than a `u32` holds — the whole reason the
        // upstream signature is `u64`. Asserted on `span` rather than by generating: keygen
        // builds one Merkle leaf per slot, so a real full-lifetime key is 2^32 WOTS keygens,
        // which is not a unit test at any timeout. This checks the arithmetic that the width
        // actually threatens.
        assert_eq!(span(&(0..=u32::MAX)).unwrap(), (0, 1u64 << 32));

        // And that the pair lands inside what upstream accepts: it rejects
        // `activation_slot + num_active_slots > 1 << LOG_LIFETIME`, so the full range sits
        // exactly on the boundary rather than one past it.
        let (start, count) = span(&(0..=u32::MAX)).unwrap();
        assert_eq!(start + count, 1u64 << xmss::LOG_LIFETIME);

        // The off-by-one this is really guarding: an inclusive range of one slot is one slot.
        assert_eq!(span(&(7..=7)).unwrap(), (7, 1));
    }

    #[test]
    fn trailing_bytes_are_rejected() {
        // postcard's `from_bytes` stops at the end of the value and ignores whatever follows,
        // which would give one key many encodings. `SingleMessageAggregateSignature::from_bytes`
        // guards against this with `take_from_bytes`; so does this.
        let sk = SecretKey::from_seed([6u8; 32], 100..=115).unwrap();
        let mut bytes = sk.to_bytes();
        bytes.push(0);
        assert!(matches!(SecretKey::from_bytes(&bytes), Err(Error::MalformedSecretKey)));
    }

    #[test]
    fn debug_does_not_print_key_material() {
        // A security property, not formatting taste. `#[derive(Debug)]` on the newtype delegates
        // to `XmssSecretKey`'s hand-written impl, which prints only the slot range and split
        // level. If that upstream impl ever becomes a derive, the seed and the whole top tree
        // start appearing in every log line that formats a key — and this test fails first.
        let sk = SecretKey::from_seed([0xab; 32], 100..=115).unwrap();
        let rendered = format!("{sk:?}");
        assert!(!rendered.contains("seed"), "{rendered}");
        assert!(!rendered.contains("top"), "{rendered}");
        assert!(!rendered.contains("171"), "seed byte 0xab leaked: {rendered}");
        // The non-exhaustive marker: whatever else the upstream struct gains stays unprinted.
        assert!(rendered.contains(".."), "{rendered}");
    }

    #[test]
    fn the_handle_is_send_and_sync() {
        // `sign` takes `&self` because the cache is behind a `Mutex`. That is only useful if the
        // handle can actually cross threads, and only sound if nothing non-`Sync` creeps in.
        const fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<SecretKey>();
    }
}
