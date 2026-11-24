namespace Ethereum.PostQuantum;

/// <summary>A raw signature with the 32-byte public key and 32-byte message it signs.</summary>
public sealed class SignedMessage : IEquatable<SignedMessage>
{
    private readonly byte[] _publicKey;
    private readonly byte[] _message;
    private readonly byte[] _signature;

    /// <summary>Creates a signed message from a copy of the public key, message and signature.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public SignedMessage(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message, ReadOnlySpan<byte> signature)
    {
        Native.RequireLength(publicKey, LeanPq.PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, LeanPq.MessageLength, nameof(message));
        _publicKey = publicKey.ToArray();
        _message = message.ToArray();
        _signature = signature.ToArray();
    }

    /// <summary>The 32-byte public key.</summary>
    public ReadOnlySpan<byte> PublicKey => _publicKey;

    /// <summary>The 32-byte message.</summary>
    public ReadOnlySpan<byte> Message => _message;

    /// <summary>The signature.</summary>
    public ReadOnlySpan<byte> Signature => _signature;

    /// <summary>Writes this entry's <c>pk|msg|sig</c> record, requiring a <paramref name="signatureLength"/>-byte signature.</summary>
    internal void WriteRecord(Span<byte> record, int signatureLength, string scheme)
    {
        if (_signature.Length != signatureLength)
        {
            throw new ArgumentException($"{scheme} signature must be exactly {signatureLength} bytes, got {_signature.Length}");
        }
        _publicKey.CopyTo(record);
        _message.CopyTo(record[LeanPq.PublicKeyLength..]);
        _signature.CopyTo(record[Native.ClaimLength..]);
    }

    /// <inheritdoc/>
    public bool Equals(SignedMessage? other) =>
        other is not null
        && _publicKey.AsSpan().SequenceEqual(other._publicKey)
        && _message.AsSpan().SequenceEqual(other._message)
        && _signature.AsSpan().SequenceEqual(other._signature);

    /// <inheritdoc/>
    public override bool Equals(object? obj) => Equals(obj as SignedMessage);

    /// <inheritdoc/>
    public override int GetHashCode()
    {
        HashCode hash = new();
        hash.AddBytes(_publicKey);
        hash.AddBytes(_message);
        hash.AddBytes(_signature);
        return hash.ToHashCode();
    }

    /// <inheritdoc/>
    public override string ToString() =>
        $"SignedMessage[PublicKey={Convert.ToHexStringLower(_publicKey)}, Message={Convert.ToHexStringLower(_message)}]";
}
