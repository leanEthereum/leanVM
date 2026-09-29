//! What the `leanxmss` guest checks: a run of signatures, each with its own claim.
//!
//! The guest outputs the digest of the claims, so a proof says all of them hold.

use crate::*;

/// One signature and its claim: that a key signed a message at an epoch.
///
/// The advice holds entries back to back, in this layout.
#[derive(Clone, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Entry {
    /// Who signed.
    pub public_key: PublicKey,
    /// When, in a word of its own so the entry stays word-aligned.
    pub epoch: u64,
    /// What was signed.
    pub message: Message,
    /// The signature the claim rests on.
    pub signature: Signature,
}

/// Words of an entry's claim: the fields before the signature.
const CLAIM_WORDS: usize = (PUB_KEY_SIZE + 8 + 32) / 8;
/// Words of an entry.
const ENTRY_WORDS: usize = size_of::<Entry>() / 8;

// Words only: no padding, and any words are an entry.
const _: () = assert!(align_of::<Entry>() == 8);
const _: () = assert!(size_of::<Entry>() == 8 * CLAIM_WORDS + SIG_SIZE);

impl Entry {
    pub fn new(public_key: PublicKey, epoch: Epoch, message: Message, signature: Signature) -> Self {
        Self {
            public_key,
            epoch: epoch.into(),
            message,
            signature,
        }
    }

    /// The entry as the words the advice holds.
    pub fn as_words(&self) -> &[u64; ENTRY_WORDS] {
        // SAFETY: an entry is its words, with no padding (asserted above).
        unsafe { &*(self as *const Self).cast() }
    }
}

/// The first `n` entries laid out in some words, read in place, or `None` if they do not fit.
pub fn entries(words: &[u64], n: usize) -> Option<&[Entry]> {
    let words = words.get(..n.checked_mul(ENTRY_WORDS)?)?;
    // SAFETY: the words hold `n` entries exactly, aligned, and any words are entries (see above).
    Some(unsafe { core::slice::from_raw_parts(words.as_ptr().cast(), n) })
}

/// Verify every entry, and return the BLAKE2s digest of their claims in order, as words.
///
/// # Errors
///
/// The index of the first entry whose signature fails, and why.
pub fn verify_batch(entries: &[Entry]) -> Result<[u64; 4], (usize, VerifyError)> {
    let mut claims = Blake2s::new();
    for (i, entry) in entries.iter().enumerate() {
        // An epoch past `2^32 - 1` would be claimed whole but verified truncated.
        let epoch = Epoch::try_from(entry.epoch).map_err(|_| (i, VerifyError::EpochOutOfRange))?;
        verify(&entry.public_key, epoch, &entry.message, &entry.signature).map_err(|e| (i, e))?;
        // The claim is the entry's first 9 words: key, epoch, message.
        claims.update_words(&entry.as_words()[..CLAIM_WORDS]);
    }
    Ok(claims.finalize_words())
}
