namespace Ethereum.PostQuantum;

/// <summary>
/// A stateful leanXMSS secret key that signs at unsigned 32-bit leaf indices. Never sign two
/// different messages at the same leaf index. Dispose it promptly to release its native allocation.
/// </summary>
public sealed unsafe class XmssSecretKey : IDisposable
{
    private readonly XmssKeyHandle _handle;

    private XmssSecretKey(XmssKeyHandle handle) => _handle = handle;

    /// <summary>Generates a key from fresh randomness.</summary>
    public static XmssSecretKey Generate() =>
        new(Native.Created(Native.XmssGenerate(out XmssKeyHandle handle), handle));

    /// <summary>Derives a key from a 32-byte seed; the seed is the key's entire secret material.</summary>
    /// <exception cref="ArgumentException">The seed is not 32 bytes.</exception>
    public static XmssSecretKey FromSeed(ReadOnlySpan<byte> seed)
    {
        Native.RequireLength(seed, LeanPq.SeedLength, nameof(seed));
        return FromBytes(seed);
    }

    /// <summary>Restores a key from <see cref="ToBytes"/>.</summary>
    /// <exception cref="LeanPqException">The bytes are not a key.</exception>
    public static XmssSecretKey FromBytes(ReadOnlySpan<byte> bytes)
    {
        fixed (byte* data = bytes)
        {
            return new(Native.Created(Native.XmssFromBytes(data, (nuint)bytes.Length, out XmssKeyHandle handle), handle));
        }
    }

    /// <summary>
    /// Loads a key from its 32-byte seed, its 32-byte public key and the bytes of
    /// <see cref="CacheToBytes"/>, building no tree. The cache is checked against the public key.
    /// </summary>
    /// <exception cref="ArgumentException">The seed or public key is not 32 bytes.</exception>
    /// <exception cref="LeanPqException">The cache is not this key's.</exception>
    public static XmssSecretKey FromCacheBytes(ReadOnlySpan<byte> seed, ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> cache)
    {
        Native.RequireLength(seed, LeanPq.SeedLength, nameof(seed));
        Native.RequireLength(publicKey, LeanPq.PublicKeyLength, nameof(publicKey));
        fixed (byte* seedPointer = seed)
        fixed (byte* publicKeyPointer = publicKey)
        fixed (byte* cachePointer = cache)
        {
            int status = Native.XmssFromCacheBytes(
                seedPointer, (nuint)seed.Length,
                publicKeyPointer, (nuint)publicKey.Length,
                cachePointer, (nuint)cache.Length,
                out XmssKeyHandle handle);
            return new(Native.Created(status, handle));
        }
    }

    /// <summary>Returns the 32-byte secret seed.</summary>
    public byte[] ToBytes() => Native.Take(Native.XmssToBytes(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Returns the trees the key holds, without any secret.</summary>
    public byte[] CacheToBytes() => Native.Take(Native.XmssCacheToBytes(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Returns the 32-byte public key.</summary>
    public byte[] GetPublicKey() => Native.Take(Native.XmssPublicKey(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Precomputes the signing state for <paramref name="leafIndex"/> so a later <see cref="Sign"/> is fast.</summary>
    public void Prepare(uint leafIndex) => Native.Check(Native.XmssPrepare(_handle, leafIndex));

    /// <summary>Signs a 32-byte message at a leaf index, returning a 2404-byte signature.</summary>
    /// <exception cref="ArgumentException">The message is not 32 bytes.</exception>
    public byte[] Sign(ReadOnlySpan<byte> message, uint leafIndex)
    {
        Native.RequireLength(message, LeanPq.MessageLength, nameof(message));
        fixed (byte* data = message)
        {
            return Native.Take(Native.XmssSign(_handle, data, (nuint)message.Length, leafIndex, out Native.Buffer buffer), buffer);
        }
    }

    /// <inheritdoc/>
    public void Dispose() => _handle.Dispose();
}
