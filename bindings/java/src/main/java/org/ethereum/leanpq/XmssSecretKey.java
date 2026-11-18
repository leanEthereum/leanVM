package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.Objects;

/**
 * A stateful leanXMSS secret key that signs at unsigned 32-bit leaf indices. Never sign two
 * different messages at the same leaf index. Close it promptly to release its native allocation.
 */
public final class XmssSecretKey implements AutoCloseable {
    private final NativeHandle handle;

    private XmssSecretKey(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroyXmss);
    }

    /** Generates a key from fresh randomness. */
    public static XmssSecretKey generate() {
        return new XmssSecretKey(Native.xmssGenerate());
    }

    /** Derives a key from a 32-byte seed; the seed is the key's entire secret material. */
    public static XmssSecretKey fromSeed(byte[] seed) {
        return new XmssSecretKey(Native.xmssFromBytes(Native.requireLength(seed, Native.SEED_LENGTH, "seed")));
    }

    /** Restores a key from {@link #toBytes()}. */
    public static XmssSecretKey fromBytes(byte[] bytes) {
        return new XmssSecretKey(Native.xmssFromBytes(Objects.requireNonNull(bytes, "bytes")));
    }

    /** Returns the 32-byte secret seed. */
    public byte[] toBytes() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.xmssToBytes(borrowed.pointer());
        }
    }

    /** Returns the 32-byte public key. */
    public byte[] publicKey() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.xmssPublicKey(borrowed.pointer());
        }
    }

    /** Precomputes the signing state for {@code leafIndex} so a later {@link #sign} is fast. */
    public void prepare(long leafIndex) {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            Native.xmssPrepare(borrowed.pointer(), leafIndex);
        }
    }

    /** Signs a 32-byte message at an unsigned 32-bit leaf index, returning a 2404-byte signature. */
    public byte[] sign(byte[] message, long leafIndex) {
        Native.requireLength(message, Native.MESSAGE_LENGTH, "message");
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.xmssSign(borrowed.pointer(), message, leafIndex);
        }
    }

    @Override
    public void close() {
        handle.close();
    }
}
