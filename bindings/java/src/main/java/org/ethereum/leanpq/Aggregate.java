package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * A verified proof that every listed public key signed its message, across leanXMSS and
 * leanSPHINCS. Its encoding is the proof alone: send the claims alongside it, or let the receiver
 * rebuild them, and check it with {@link Sidecar#verify(byte[], List, List)}.
 */
public final class Aggregate implements AutoCloseable {
    private final NativeHandle handle;

    Aggregate(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroyAggregate);
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

    private static List<SignatureClaim> claims(byte[] records) {
        if (records.length % Native.CLAIM_LENGTH != 0) {
            throw new LeanPqException("native claim data is not a multiple of " + Native.CLAIM_LENGTH + " bytes");
        }
        List<SignatureClaim> claims = new ArrayList<>(records.length / Native.CLAIM_LENGTH);
        for (int offset = 0; offset < records.length; offset += Native.CLAIM_LENGTH) {
            claims.add(new SignatureClaim(
                Arrays.copyOfRange(records, offset, offset + Native.PUBLIC_KEY_LENGTH),
                Arrays.copyOfRange(records, offset + Native.PUBLIC_KEY_LENGTH, offset + Native.CLAIM_LENGTH)));
        }
        return List.copyOf(claims);
    }
}
