package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * A connection to a leanVM sidecar, the separate process that proves and verifies aggregates.
 * Safe to share between threads: its calls run one at a time. A broken connection is reopened on
 * the next call. Unix only: on other platforms {@link #connect(Path)} and {@link #start(Path, Path)}
 * throw {@link LeanPqException}.
 */
public final class Sidecar implements AutoCloseable {
    private final NativeHandle handle;

    private Sidecar(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroySidecar);
    }

    /** Connects to the sidecar listening on the Unix socket {@code socket}. */
    public static Sidecar connect(Path socket) {
        return new Sidecar(Native.sidecarConnect(Objects.requireNonNull(socket, "socket")));
    }

    /** Like {@link #start(Path, Path, int)} with one thread per core. */
    public static Sidecar start(Path binary, Path socket) {
        return start(binary, socket, 0);
    }

    /**
     * Launches the {@code leanvm-sidecar} executable {@code binary} on {@code socket} with
     * {@code threads} threads (0: one per core), waits until it listens, and connects to it;
     * {@link #close()} stops it. Its log goes to the socket's path with {@code .log} appended. Throws
     * {@link LeanPqException} if a sidecar already listens there.
     */
    public static Sidecar start(Path binary, Path socket, int threads) {
        if (threads < 0) {
            throw new IllegalArgumentException("threads must not be negative");
        }
        return new Sidecar(Native.sidecarStart(Objects.requireNonNull(binary, "binary"), Objects.requireNonNull(socket, "socket"), threads));
    }

    /** The prover the sidecar runs: {@code "experimental"} or {@code "stable"}, which make the same proofs. */
    public String prover() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.sidecarProver(borrowed.pointer());
        }
    }

    /**
     * Proves the union of the children's claims and the raw signatures' claims. Raw signatures are
     * verified first; at most 16 children are accepted, and the input must not be empty. The
     * children stay owned by the caller.
     */
    public Aggregate aggregate(List<Aggregate> children, List<SignedMessage> xmss, List<SignedMessage> sphincs) {
        Objects.requireNonNull(children, "children");
        byte[] xmssRecords = signedRecords(Objects.requireNonNull(xmss, "xmss"), Native.XMSS_SIGNATURE_LENGTH, "leanXMSS");
        byte[] sphincsRecords = signedRecords(Objects.requireNonNull(sphincs, "sphincs"), Native.SPHINCS_SIGNATURE_LENGTH, "leanSPHINCS");
        List<NativeHandle.Borrow> borrowed = new ArrayList<>(children.size());
        try (NativeHandle.Borrow sidecar = handle.borrow()) {
            for (Aggregate child : children) {
                borrowed.add(Objects.requireNonNull(child, "child").borrow());
            }
            List<MemorySegment> pointers = borrowed.stream().map(NativeHandle.Borrow::pointer).toList();
            // The counts come from the packed records, not from the lists, whose sizes may have changed.
            return new Aggregate(Native.sidecarAggregate(
                sidecar.pointer(),
                pointers,
                xmssRecords, xmssRecords.length / (Native.CLAIM_LENGTH + Native.XMSS_SIGNATURE_LENGTH),
                sphincsRecords, sphincsRecords.length / (Native.CLAIM_LENGTH + Native.SPHINCS_SIGNATURE_LENGTH)));
        } finally {
            for (int index = borrowed.size() - 1; index >= 0; index--) {
                borrowed.get(index).close();
            }
        }
    }

    /**
     * Verifies that {@code bytes}, from {@link Aggregate#toBytes()}, prove exactly the given claims,
     * in any order; a repeated claim counts once. Throws {@link LeanPqException} if the bytes are not
     * a proof of exactly these claims.
     */
    public Aggregate verify(byte[] bytes, List<SignatureClaim> xmssClaims, List<SignatureClaim> sphincsClaims) {
        Objects.requireNonNull(bytes, "bytes");
        byte[] xmssRecords = claimRecords(Objects.requireNonNull(xmssClaims, "xmssClaims"));
        byte[] sphincsRecords = claimRecords(Objects.requireNonNull(sphincsClaims, "sphincsClaims"));
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return new Aggregate(Native.sidecarVerify(borrowed.pointer(),
                bytes, xmssRecords, xmssRecords.length / Native.CLAIM_LENGTH, sphincsRecords, sphincsRecords.length / Native.CLAIM_LENGTH));
        }
    }

    /**
     * Stops the sidecar {@link #start(Path, Path)} launched at once, failing calls in progress, and
     * closes the connection; the handle is freed once those calls return. Later calls throw
     * {@link IllegalStateException}. Idempotent. An unreachable started sidecar is stopped when the
     * Cleaner frees it.
     */
    @Override
    public void close() {
        try (NativeHandle.Borrow borrowed = handle.borrowIfOpen()) {
            if (borrowed != null) {
                Native.closeSidecar(borrowed.pointer());
            }
        } finally {
            handle.close();
        }
    }

    private static byte[] signedRecords(List<SignedMessage> entries, int signatureLength, String scheme) {
        int recordLength = Native.CLAIM_LENGTH + signatureLength;
        int count = entries.size();
        byte[] records = new byte[Math.multiplyExact(count, recordLength)];
        for (int index = 0; index < count; index++) {
            Objects.requireNonNull(entries.get(index), "signed message")
                .writeRecord(records, index * recordLength, signatureLength, scheme);
        }
        return records;
    }

    private static byte[] claimRecords(List<SignatureClaim> claims) {
        int count = claims.size();
        byte[] records = new byte[Math.multiplyExact(count, Native.CLAIM_LENGTH)];
        for (int index = 0; index < count; index++) {
            Objects.requireNonNull(claims.get(index), "claim").writeRecord(records, index * Native.CLAIM_LENGTH);
        }
        return records;
    }
}
