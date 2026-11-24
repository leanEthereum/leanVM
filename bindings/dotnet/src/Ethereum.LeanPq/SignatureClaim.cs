namespace Ethereum.PostQuantum;

/// <summary>A claim proven by an <see cref="Aggregate"/>: the 32-byte public key signed the 32-byte message.</summary>
public sealed class SignatureClaim : IEquatable<SignatureClaim>
{
    private readonly byte[] _publicKey;
    private readonly byte[] _message;

    /// <summary>Creates a claim from a copy of the public key and message.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public SignatureClaim(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message)
    {
        Native.RequireLength(publicKey, LeanPq.PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, LeanPq.MessageLength, nameof(message));
        _publicKey = publicKey.ToArray();
        _message = message.ToArray();
    }

    /// <summary>The 32-byte public key.</summary>
    public ReadOnlySpan<byte> PublicKey => _publicKey;

    /// <summary>The 32-byte message.</summary>
    public ReadOnlySpan<byte> Message => _message;

    /// <summary>Writes this claim's 64-byte <c>pk|msg</c> record.</summary>
    internal void WriteRecord(Span<byte> record)
    {
        _publicKey.CopyTo(record);
        _message.CopyTo(record[LeanPq.PublicKeyLength..]);
    }

    /// <inheritdoc/>
    public bool Equals(SignatureClaim? other) =>
        other is not null && _publicKey.AsSpan().SequenceEqual(other._publicKey) && _message.AsSpan().SequenceEqual(other._message);

    /// <inheritdoc/>
    public override bool Equals(object? obj) => Equals(obj as SignatureClaim);

    /// <inheritdoc/>
    public override int GetHashCode()
    {
        HashCode hash = new();
        hash.AddBytes(_publicKey);
        hash.AddBytes(_message);
        return hash.ToHashCode();
    }

    /// <inheritdoc/>
    public override string ToString() =>
        $"SignatureClaim[PublicKey={Convert.ToHexStringLower(_publicKey)}, Message={Convert.ToHexStringLower(_message)}]";
}
