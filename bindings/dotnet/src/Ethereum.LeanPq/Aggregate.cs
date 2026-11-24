namespace Ethereum.PostQuantum;

/// <summary>
/// A verified proof that every listed public key signed its message, across leanXMSS and
/// leanSPHINCS. Its encoding is the proof alone: send the claims alongside it, or let the receiver
/// rebuild them, and check it with <see cref="FromBytes"/>.
/// </summary>
public sealed unsafe class Aggregate : IDisposable
{
    internal Aggregate(AggregateHandle handle) => Handle = handle;

    internal AggregateHandle Handle { get; }

    /// <summary>
    /// Verifies that <paramref name="proof"/>, from <see cref="ToBytes"/>, proves exactly the given
    /// claims, in any order; a repeated claim counts once.
    /// </summary>
    /// <exception cref="LeanPqException">The bytes are not a proof of exactly these claims.</exception>
    public static Aggregate FromBytes(ReadOnlySpan<byte> proof, IReadOnlyList<SignatureClaim> xmssClaims, IReadOnlyList<SignatureClaim> sphincsClaims)
    {
        byte[] xmssRecords = ClaimRecords(xmssClaims);
        byte[] sphincsRecords = ClaimRecords(sphincsClaims);
        fixed (byte* proofPointer = proof)
        fixed (byte* xmssPointer = xmssRecords)
        fixed (byte* sphincsPointer = sphincsRecords)
        {
            int status = Native.AggregateFromBytes(
                proofPointer, (nuint)proof.Length,
                xmssPointer, (nuint)(xmssRecords.Length / Native.ClaimLength),
                sphincsPointer, (nuint)(sphincsRecords.Length / Native.ClaimLength),
                out AggregateHandle handle);
            return new(Native.Created(status, handle));
        }
    }

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

    /// <summary>Packs claims as the native side takes them: concatenated 64-byte <c>pk|msg</c> records.</summary>
    internal static byte[] ClaimRecords(IReadOnlyList<SignatureClaim> claims)
    {
        ArgumentNullException.ThrowIfNull(claims);
        byte[] records = new byte[checked(claims.Count * Native.ClaimLength)];
        for (int index = 0; index < claims.Count; index++)
        {
            SignatureClaim claim = claims[index] ?? throw new ArgumentNullException(nameof(claims), "a claim is null");
            claim.WriteRecord(records.AsSpan(index * Native.ClaimLength, Native.ClaimLength));
        }
        return records;
    }

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
