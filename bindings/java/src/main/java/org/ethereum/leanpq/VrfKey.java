package org.ethereum.leanpq;

import java.lang.foreign.MemorySegment;
import java.util.Objects;

/**
 * A key of the consensus VRF tree, pruned to a range of unsigned 32-bit slots: a 32-byte seed and
 * the range {@code [start, end)}, which together fix the root, so keep both. Close the key promptly
 * to release its native allocation.
 */
public final class VrfKey implements AutoCloseable {
    private final NativeHandle handle;

    private VrfKey(MemorySegment pointer) {
        handle = new NativeHandle(pointer, Native::destroyVrfKey);
    }

    /**
     * The key of a 32-byte seed with leaves for the slots {@code [start, end)}, a nonempty range
     * ending at most at 2^31. Hashes every leaf of the range once.
     */
    public static VrfKey fromSeed(byte[] seed, long start, long end) {
        return new VrfKey(Native.vrfKeyNew(Native.requireLength(seed, Native.SEED_LENGTH, "seed"), start, end));
    }

    /**
     * Loads a key from its 32-byte seed and the bytes of {@link #cacheToBytes()}, hashing about
     * sqrt(end - start) nodes. The cache is not checked, and a wrong one gives a wrong root, so
     * compare {@link #root()} with the registered root before revealing a proof.
     */
    public static VrfKey fromCacheBytes(byte[] seed, byte[] cache) {
        Native.requireLength(seed, Native.SEED_LENGTH, "seed");
        return new VrfKey(Native.vrfKeyFromCacheBytes(seed, Objects.requireNonNull(cache, "cache")));
    }

    /** Returns the range and the cached layer of the tree, without any secret. */
    public byte[] cacheToBytes() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.vrfCacheToBytes(borrowed.pointer());
        }
    }

    /** Returns the 32-byte root, the validator's registered VRF root. */
    public byte[] root() {
        try (NativeHandle.Borrow borrowed = handle.borrow()) {
            return Native.vrfRoot(borrowed.pointer());
        }
    }

    /** Returns the 1024-byte proof of a slot of the range: the leaf, then its 31 siblings, bottom-up. */
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
