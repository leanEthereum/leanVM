package org.ethereum.leanpq;

import java.util.Objects;

/** Verifies single signatures and VRF proofs; {@link Sidecar} aggregates signatures. */
public final class LeanPq {
    private LeanPq() {}

    /** Returns whether the 2404-byte leanXMSS signature is valid for the public key and message. */
    public static boolean xmssVerify(byte[] publicKey, byte[] message, byte[] signature) {
        return Native.xmssVerify(
            Native.requireLength(publicKey, Native.PUBLIC_KEY_LENGTH, "publicKey"),
            Native.requireLength(message, Native.MESSAGE_LENGTH, "message"),
            Objects.requireNonNull(signature, "signature"));
    }

    /** Returns whether the 7740-byte leanSPHINCS signature is valid for the public key and message. */
    public static boolean sphincsVerify(byte[] publicKey, byte[] message, byte[] signature) {
        return Native.sphincsVerify(
            Native.requireLength(publicKey, Native.PUBLIC_KEY_LENGTH, "publicKey"),
            Native.requireLength(message, Native.MESSAGE_LENGTH, "message"),
            Objects.requireNonNull(signature, "signature"));
    }

    /**
     * Returns whether a 1024-byte VRF proof opens the slot under a 32-byte root, as
     * {@code is_valid_vrf_proof}.
     */
    public static boolean vrfVerify(byte[] root, long slot, byte[] proof) {
        return Native.vrfVerify(
            Native.requireLength(root, Native.VRF_ROOT_LENGTH, "root"),
            slot,
            Objects.requireNonNull(proof, "proof"));
    }
}
