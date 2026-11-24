namespace Ethereum.PostQuantum;

/// <summary>
/// A VRF key: a 32-byte seed and its slots <c>[start, end)</c>, which fix the root, so keep both.
/// Dispose it to free its native memory.
/// </summary>
public sealed unsafe class VrfKey : IDisposable
{
    private readonly VrfKeyHandle _handle;

    private VrfKey(VrfKeyHandle handle) => _handle = handle;

    /// <summary>Builds the key, hashing every slot of the range, which must be nonempty and end by 2^31.</summary>
    /// <exception cref="ArgumentException">The seed is not 32 bytes.</exception>
    /// <exception cref="LeanPqException">The range is empty or ends past 2^31.</exception>
    public static VrfKey FromSeed(ReadOnlySpan<byte> seed, uint start, uint end)
    {
        Native.RequireLength(seed, LeanPq.SeedLength, nameof(seed));
        fixed (byte* data = seed)
        {
            return new(Native.Created(Native.VrfKeyNew(data, (nuint)seed.Length, start, end, out VrfKeyHandle handle), handle));
        }
    }

    /// <summary>
    /// Rebuilds a key from its seed, its root and a cache from <see cref="CacheToBytes"/>, without
    /// hashing the range.
    /// </summary>
    /// <exception cref="ArgumentException">The seed or root is not 32 bytes.</exception>
    /// <exception cref="LeanPqException">The cache is malformed or does not lead to the root.</exception>
    public static VrfKey FromCacheBytes(ReadOnlySpan<byte> seed, ReadOnlySpan<byte> root, ReadOnlySpan<byte> cache)
    {
        Native.RequireLength(seed, LeanPq.SeedLength, nameof(seed));
        Native.RequireLength(root, LeanPq.VrfRootLength, nameof(root));
        fixed (byte* seedPointer = seed)
        fixed (byte* rootPointer = root)
        fixed (byte* cachePointer = cache)
        {
            int status = Native.VrfKeyFromCacheBytes(
                seedPointer, (nuint)seed.Length,
                rootPointer, (nuint)root.Length,
                cachePointer, (nuint)cache.Length,
                out VrfKeyHandle handle);
            return new(Native.Created(status, handle));
        }
    }

    /// <summary>Encodes the key's cache: its range and cached layer, no secret.</summary>
    public byte[] CacheToBytes() => Native.Take(Native.VrfKeyCacheToBytes(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Returns the 32-byte root, which the validator registers.</summary>
    public byte[] GetRoot() => Native.Take(Native.VrfKeyRoot(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Returns the 1024-byte proof of a slot of the range: its secret, then its leaf's 31 siblings.</summary>
    /// <exception cref="LeanPqException">The slot is outside the range.</exception>
    public byte[] GetProof(uint slot) => Native.Take(Native.VrfKeyProof(_handle, slot, out Native.Buffer buffer), buffer);

    /// <inheritdoc/>
    public void Dispose() => _handle.Dispose();
}
