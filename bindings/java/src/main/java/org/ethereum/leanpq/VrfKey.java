package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.Objects;

/**
 * A VRF key: a 32-byte seed and its slots {@code [start, end)}, which fix the root, so keep both.
 * Close it to free its native memory.
 */
public final class VrfKey implements AutoCloseable {
    private final NativeHandle handle;

    private VrfKey(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroyVrfKey);
    }

    /** Builds the key, hashing every slot of the range, which must be nonempty and end by 2^31. */
    public static VrfKey fromSeed(byte[] seed, long start, long end) {
        return new VrfKey(Native.vrfKeyNew(Native.requireLength(seed, Native.SEED_LENGTH, "seed"), start, end));
    }

    /**
     * Rebuilds a key from its seed, its root and a cache from {@link #cacheToBytes()}, without
     * hashing the range. Throws {@link LeanPqException} if the cache is malformed or does not lead to
     * the root.
     */
    public static VrfKey fromCacheBytes(byte[] seed, byte[] root, byte[] cache) {
        Native.requireLength(seed, Native.SEED_LENGTH, "seed");
        Native.requireLength(root, Native.VRF_ROOT_LENGTH, "root");
        return new VrfKey(Native.vrfKeyFromCacheBytes(seed, root, Objects.requireNonNull(cache, "cache")));
    }

    /** Encodes the key's cache: its range and cached layer, no secret. */
    public byte[] cacheToBytes() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.vrfCacheToBytes(borrowed.pointer());
        }
    }

    /** Returns the 32-byte root, which the validator registers. */
    public byte[] root() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.vrfRoot(borrowed.pointer());
        }
    }

    /** Returns the 1024-byte proof of a slot of the range: its secret, then its leaf's 31 siblings. */
    public byte[] proof(long slot) {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.vrfProof(borrowed.pointer(), slot);
        }
    }

    @Override
    public void close() {
        handle.close();
    }
}
