namespace Ethereum.LeanPq;

/// <summary>
/// A verified proof that every listed public key signed its message, across leanXMSS and
/// leanSPHINCS. Its encoding is the proof alone: send the claims alongside it, or let the receiver
/// rebuild them, and check it with <see cref="Sidecar.Verify"/>.
/// </summary>
public sealed class Aggregate : IDisposable
{
    internal Aggregate(AggregateHandle handle) => Handle = handle;

    internal AggregateHandle Handle { get; }

    /// <summary>Returns the proof alone, without its claims.</summary>
    public byte[] ToBytes() => Native.Take(Native.AggregateToBytes(Handle, out Native.Buffer buffer), buffer);

    /// <summary>The proven leanXMSS claims, strictly sorted.</summary>
    public IReadOnlyList<SignatureClaim> GetXmssClaims() =>
        Claims(Native.Take(Native.AggregateXmssClaims(Handle, out Native.Buffer buffer), buffer));

    /// <summary>The proven leanSPHINCS claims, strictly sorted.</summary>
    public IReadOnlyList<SignatureClaim> GetSphincsClaims() =>
        Claims(Native.Take(Native.AggregateSphincsClaims(Handle, out Native.Buffer buffer), buffer));

    /// <inheritdoc/>
    public void Dispose() => Handle.Dispose();

    private static SignatureClaim[] Claims(byte[] records)
    {
        if (records.Length % Native.ClaimLength != 0)
        {
            throw new LeanPqException($"native claim data is not a multiple of {Native.ClaimLength} bytes");
        }
        SignatureClaim[] claims = new SignatureClaim[records.Length / Native.ClaimLength];
        for (int index = 0; index < claims.Length; index++)
        {
            ReadOnlySpan<byte> record = records.AsSpan(index * Native.ClaimLength, Native.ClaimLength);
            claims[index] = new SignatureClaim(record[..LeanPq.PublicKeyLength], record[LeanPq.PublicKeyLength..]);
        }
        return claims;
    }
}
