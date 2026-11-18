package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.Objects;

/**
 * A stateless leanSPHINCS secret key: its 32-byte seed. It signs at most 2^30 messages, and signing
 * is deterministic. Close it promptly to release its native allocation.
 */
public final class SphincsSecretKey implements AutoCloseable {
    private final NativeHandle handle;

    private SphincsSecretKey(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroySphincs);
    }

    /** Generates a key from fresh randomness. */
    public static SphincsSecretKey generate() {
        return new SphincsSecretKey(Native.sphincsGenerate());
    }

    /** Derives a key from a 32-byte seed; the seed is the key's entire secret material. */
    public static SphincsSecretKey fromSeed(byte[] seed) {
        return new SphincsSecretKey(Native.sphincsFromSeed(Native.requireLength(seed, Native.SEED_LENGTH, "seed")));
    }

    /** Restores a key from {@link #toBytes()}. */
    public static SphincsSecretKey fromBytes(byte[] bytes) {
        return new SphincsSecretKey(Native.sphincsFromBytes(Objects.requireNonNull(bytes, "bytes")));
    }

    /** Returns the 32-byte secret material: the seed. */
    public byte[] toBytes() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.sphincsToBytes(borrowed.pointer());
        }
    }

    /** Returns the 32-byte public key. */
    public byte[] publicKey() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.sphincsPublicKey(borrowed.pointer());
        }
    }

    /** Signs a 32-byte message, returning a 7740-byte signature. */
    public byte[] sign(byte[] message) {
        Native.requireLength(message, Native.MESSAGE_LENGTH, "message");
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.sphincsSign(borrowed.pointer(), message);
        }
    }

    @Override
    public void close() {
        handle.close();
    }
}
