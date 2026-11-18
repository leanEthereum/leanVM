package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * A verified proof that every listed public key signed its message, across leanXMSS and
 * leanSPHINCS. Its encoding is the proof alone: send the claims alongside it, or let the receiver
 * rebuild them, and decode it with {@link #fromBytes(byte[], List, List)}.
 */
public final class Aggregate implements AutoCloseable {
    private static final int CLAIM_LENGTH = Native.PUBLIC_KEY_LENGTH + Native.MESSAGE_LENGTH;

    private final NativeHandle handle;

    Aggregate(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroyAggregate);
    }

    /**
     * Decodes a proof from {@link #toBytes()} and verifies that it proves exactly the given claims,
     * in any order; a repeated claim counts once. Throws {@link LeanPqException} if the bytes are
     * not a proof or the proof does not prove exactly these claims.
     */
    public static Aggregate fromBytes(byte[] bytes, List<SignatureClaim> xmssClaims, List<SignatureClaim> sphincsClaims) {
        Objects.requireNonNull(bytes, "bytes");
        byte[] xmssRecords = records(Objects.requireNonNull(xmssClaims, "xmssClaims"));
        byte[] sphincsRecords = records(Objects.requireNonNull(sphincsClaims, "sphincsClaims"));
        return new Aggregate(Native.aggregateFromBytes(bytes, xmssRecords, xmssClaims.size(), sphincsRecords, sphincsClaims.size()));
    }

    /** Returns the proof alone, without its claims. */
    public byte[] toBytes() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.aggregateToBytes(borrowed.pointer());
        }
    }

    /** The proven leanXMSS claims, strictly sorted. */
    public List<SignatureClaim> xmssClaims() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return claims(Native.xmssClaims(borrowed.pointer()));
        }
    }

    /** The proven leanSPHINCS claims, strictly sorted. */
    public List<SignatureClaim> sphincsClaims() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return claims(Native.sphincsClaims(borrowed.pointer()));
        }
    }

    NativeHandle.Borrow borrow() {
        return handle.borrow();
    }

    @Override
    public void close() {
        handle.close();
    }

    private static byte[] records(List<SignatureClaim> claims) {
        byte[] records = new byte[Math.multiplyExact(claims.size(), CLAIM_LENGTH)];
        for (int index = 0; index < claims.size(); index++) {
            Objects.requireNonNull(claims.get(index), "claim").writeRecord(records, index * CLAIM_LENGTH);
        }
        return records;
    }

    private static List<SignatureClaim> claims(byte[] records) {
        if (records.length % CLAIM_LENGTH != 0) {
            throw new LeanPqException("native claim data is not a multiple of " + CLAIM_LENGTH + " bytes");
        }
        List<SignatureClaim> claims = new ArrayList<>(records.length / CLAIM_LENGTH);
        for (int offset = 0; offset < records.length; offset += CLAIM_LENGTH) {
            claims.add(new SignatureClaim(
                Arrays.copyOfRange(records, offset, offset + Native.PUBLIC_KEY_LENGTH),
                Arrays.copyOfRange(records, offset + Native.PUBLIC_KEY_LENGTH, offset + CLAIM_LENGTH)));
        }
        return List.copyOf(claims);
    }
}
