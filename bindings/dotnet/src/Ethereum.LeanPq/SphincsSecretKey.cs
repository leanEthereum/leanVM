namespace Ethereum.PostQuantum;

/// <summary>
/// A stateless leanSPHINCS secret key: its 32-byte seed. It signs at most 2^30 messages, and signing
/// is deterministic. Dispose it promptly to release its native allocation.
/// </summary>
public sealed unsafe class SphincsSecretKey : IDisposable
{
    private readonly SphincsKeyHandle _handle;

    private SphincsSecretKey(SphincsKeyHandle handle) => _handle = handle;

    /// <summary>Generates a key from fresh randomness.</summary>
    public static SphincsSecretKey Generate() =>
        new(Native.Created(Native.SphincsGenerate(out SphincsKeyHandle handle), handle));

    /// <summary>Derives a key from a 32-byte seed; the seed is the key's entire secret material.</summary>
    /// <exception cref="ArgumentException">The seed is not 32 bytes.</exception>
    public static SphincsSecretKey FromSeed(ReadOnlySpan<byte> seed)
    {
        Native.RequireLength(seed, LeanPq.SeedLength, nameof(seed));
        fixed (byte* data = seed)
        {
            return new(Native.Created(Native.SphincsFromSeed(data, (nuint)seed.Length, out SphincsKeyHandle handle), handle));
        }
    }

    /// <summary>Restores a key from <see cref="ToBytes"/>.</summary>
    /// <exception cref="LeanPqException">The bytes are not a key.</exception>
    public static SphincsSecretKey FromBytes(ReadOnlySpan<byte> bytes)
    {
        fixed (byte* data = bytes)
        {
            return new(Native.Created(Native.SphincsFromBytes(data, (nuint)bytes.Length, out SphincsKeyHandle handle), handle));
        }
    }

    /// <summary>Returns the 32-byte secret material: the seed.</summary>
    public byte[] ToBytes() => Native.Take(Native.SphincsToBytes(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Returns the 32-byte public key.</summary>
    public byte[] GetPublicKey() => Native.Take(Native.SphincsPublicKey(_handle, out Native.Buffer buffer), buffer);

    /// <summary>Signs a 32-byte message, returning a 7740-byte signature.</summary>
    /// <exception cref="ArgumentException">The message is not 32 bytes.</exception>
    public byte[] Sign(ReadOnlySpan<byte> message)
    {
        Native.RequireLength(message, LeanPq.MessageLength, nameof(message));
        fixed (byte* data = message)
        {
            return Native.Take(Native.SphincsSign(_handle, data, (nuint)message.Length, out Native.Buffer buffer), buffer);
        }
    }

    /// <inheritdoc/>
    public void Dispose() => _handle.Dispose();
}
