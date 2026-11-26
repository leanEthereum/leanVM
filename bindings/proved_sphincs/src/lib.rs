//! Internal bridge to the formally verified `lean_sphincs::verify` assembly on Linux
//! (`x86_64` and `aarch64`), falling back to safe Rust on other targets.

use lean_sphincs::{MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE};

const _: () = assert!(PUB_KEY_SIZE == 32);
const _: () = assert!(MESSAGE_LEN == 32);
const _: () = assert!(SIG_SIZE == 7740);

/// Whether this target links and runs the formally verified `sphincs_verify` assembly.
pub const USING_PROVED_ASM: bool = cfg!(proved_sphincs_asm);

#[cfg(proved_sphincs_asm)]
extern "C" {
    fn sphincs_verify(
        pk: *const [u8; PUB_KEY_SIZE],
        msg: *const [u8; MESSAGE_LEN],
        sig: *const [u8; SIG_SIZE],
    ) -> u64;
}

/// Verifies a leanSPHINCS signature over raw public key, message, and signature bytes.
#[must_use]
pub fn verify_bytes(
    pk: &[u8; PUB_KEY_SIZE],
    msg: &[u8; MESSAGE_LEN],
    sig: &[u8; SIG_SIZE],
) -> bool {
    #[cfg(proved_sphincs_asm)]
    {
        // SAFETY: `pk`, `msg`, and `sig` are non-null pointers to 32, 32, and 7740 readable
        // bytes respectively. `sphincs_verify` only reads those ranges and uses its own stack
        // and read-only data sections, returning 1 on acceptance and 0 on rejection.
        unsafe { sphincs_verify(pk, msg, sig) == 1 }
    }
    #[cfg(not(proved_sphincs_asm))]
    {
        let pk = lean_sphincs::LeanSphincsPublicKey::from_bytes(pk);
        let sig = lean_sphincs::LeanSphincsSignature::from_bytes(sig);
        lean_sphincs::verify(&pk, msg, &sig)
    }
}
