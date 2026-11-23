package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/** Verifies single signatures and VRF proofs, and aggregates signatures. */
public final class LeanPq {
    private LeanPq() {}

    /**
     * Starts the prover with {@code threads} threads (0: one per core). Throws
     * {@link LeanPqException} if it already runs with another count.
     */
    public static void setup(int threads) {
        if (threads < 0) {
            throw new IllegalArgumentException("threads must not be negative");
        }
        Native.setup(threads);
    }

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

    /**
     * Proves the union of the children's claims and the raw signatures' claims. Raw signatures are
     * verified first; at most 16 children are accepted, and the input must not be empty.
     */
    public static Aggregate aggregate(List<Aggregate> children, List<SignedMessage> xmss, List<SignedMessage> sphincs) {
        return aggregate(children, xmss, sphincs, null, null);
    }

    /**
     * {@link #aggregate(List, List, List)}, but the result proves exactly the given claims, in any
     * order, a repeat counting once; each must be one the inputs cover.
     */
    public static Aggregate aggregateOnly(
            List<Aggregate> children, List<SignedMessage> xmss, List<SignedMessage> sphincs,
            List<SignatureClaim> xmssClaims, List<SignatureClaim> sphincsClaims) {
        return aggregate(
            children, xmss, sphincs,
            Aggregate.claimRecords(Objects.requireNonNull(xmssClaims, "xmssClaims")),
            Aggregate.claimRecords(Objects.requireNonNull(sphincsClaims, "sphincsClaims")));
    }

    /** {@code xmssClaims} and {@code sphincsClaims} are both null to prove every covered claim. */
    private static Aggregate aggregate(
            List<Aggregate> children, List<SignedMessage> xmss, List<SignedMessage> sphincs,
            byte[] xmssClaims, byte[] sphincsClaims) {
        Objects.requireNonNull(children, "children");
        byte[] xmssRecords = records(Objects.requireNonNull(xmss, "xmss"), Native.XMSS_SIGNATURE_LENGTH, "leanXMSS");
        byte[] sphincsRecords = records(Objects.requireNonNull(sphincs, "sphincs"), Native.SPHINCS_SIGNATURE_LENGTH, "leanSPHINCS");
        List<NativeHandle.Borrow> borrowed = new ArrayList<>(children.size());
        try {
            for (Aggregate child : children) {
                borrowed.add(Objects.requireNonNull(child, "child").borrow());
            }
            List<MemorySegment> pointers = borrowed.stream().map(NativeHandle.Borrow::pointer).toList();
            // The counts come from the packed records, not from the lists, whose sizes may have changed.
            long xmssCount = xmssRecords.length / (Native.CLAIM_LENGTH + Native.XMSS_SIGNATURE_LENGTH);
            long sphincsCount = sphincsRecords.length / (Native.CLAIM_LENGTH + Native.SPHINCS_SIGNATURE_LENGTH);
            if (xmssClaims == null) {
                return new Aggregate(Native.aggregate(pointers, xmssRecords, xmssCount, sphincsRecords, sphincsCount));
            }
            return new Aggregate(Native.aggregateOnly(
                pointers, xmssRecords, xmssCount, sphincsRecords, sphincsCount,
                xmssClaims, xmssClaims.length / Native.CLAIM_LENGTH,
                sphincsClaims, sphincsClaims.length / Native.CLAIM_LENGTH));
        } finally {
            for (int index = borrowed.size() - 1; index >= 0; index--) {
                borrowed.get(index).close();
            }
        }
    }

    private static byte[] records(List<SignedMessage> entries, int signatureLength, String scheme) {
        int recordLength = Native.CLAIM_LENGTH + signatureLength;
        int count = entries.size();
        byte[] records = new byte[Math.multiplyExact(count, recordLength)];
        for (int index = 0; index < count; index++) {
            Objects.requireNonNull(entries.get(index), "signed message")
                .writeRecord(records, index * recordLength, signatureLength, scheme);
        }
        return records;
    }
}
