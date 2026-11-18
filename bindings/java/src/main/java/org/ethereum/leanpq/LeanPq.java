package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/** Entry points for verification and recursive aggregation. */
public final class LeanPq {
    private static final int RECORD_PREFIX_LENGTH = Native.PUBLIC_KEY_LENGTH + Native.MESSAGE_LENGTH;

    private LeanPq() {}

    /**
     * Moves the one-time process-wide proving setup ahead of the first aggregation. Optional and
     * safe to call repeatedly.
     */
    public static void setup() {
        Native.setup();
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
     * Proves the union of the children's claims and the raw signatures' claims. Raw signatures are
     * verified first; at most 16 children are accepted, and the input must not be empty. Proving
     * runs one aggregation at a time per process. The children stay owned by the caller.
     */
    public static Aggregate aggregate(List<Aggregate> children, List<SignedMessage> xmss, List<SignedMessage> sphincs) {
        Objects.requireNonNull(children, "children");
        byte[] xmssRecords = records(Objects.requireNonNull(xmss, "xmss"), Native.XMSS_SIGNATURE_LENGTH, "leanXMSS");
        byte[] sphincsRecords = records(Objects.requireNonNull(sphincs, "sphincs"), Native.SPHINCS_SIGNATURE_LENGTH, "leanSPHINCS");
        List<NativeHandle.Borrow> borrowed = new ArrayList<>(children.size());
        try {
            for (Aggregate child : children) {
                borrowed.add(Objects.requireNonNull(child, "child").borrow());
            }
            List<MemorySegment> pointers = borrowed.stream().map(NativeHandle.Borrow::pointer).toList();
            return new Aggregate(Native.aggregate(pointers, xmssRecords, xmss.size(), sphincsRecords, sphincs.size()));
        } finally {
            for (int index = borrowed.size() - 1; index >= 0; index--) {
                borrowed.get(index).close();
            }
        }
    }

    private static byte[] records(List<SignedMessage> entries, int signatureLength, String scheme) {
        int recordLength = RECORD_PREFIX_LENGTH + signatureLength;
        byte[] records = new byte[Math.multiplyExact(entries.size(), recordLength)];
        for (int index = 0; index < entries.size(); index++) {
            Objects.requireNonNull(entries.get(index), "signed message")
                .writeRecord(records, index * recordLength, signatureLength, scheme);
        }
        return records;
    }
}
