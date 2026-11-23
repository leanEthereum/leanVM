using System.Text;

namespace Ethereum.LeanPq;

/// <summary>
/// A connection to a leanVM sidecar, the separate process that proves and verifies aggregates.
/// Safe to share between threads: its calls run one at a time. A broken connection is reopened on
/// the next call. Unix only: on other platforms <see cref="Connect"/> and <see cref="Start"/> throw
/// <see cref="LeanPqException"/>.
/// </summary>
public sealed unsafe class Sidecar : IDisposable
{
    private const int MaxChildren = 16;

    private readonly SidecarHandle _handle;

    private Sidecar(SidecarHandle handle) => _handle = handle;

    /// <summary>Connects to the sidecar listening on the Unix socket at <paramref name="socketPath"/>.</summary>
    /// <exception cref="LeanPqException">No sidecar listens there.</exception>
    public static Sidecar Connect(string socketPath)
    {
        ArgumentNullException.ThrowIfNull(socketPath);
        byte[] path = Native.PathBytes(socketPath);
        fixed (byte* pathPointer = path)
        {
            return new(Native.Created(Native.SidecarConnect(pathPointer, (nuint)path.Length, out SidecarHandle handle), handle));
        }
    }

    /// <summary>
    /// Launches the <c>leanvm-sidecar</c> executable <paramref name="binaryPath"/> on
    /// <paramref name="socketPath"/>, waits until it listens, and connects to it; <see cref="Dispose"/>
    /// stops it. Its log goes to the socket's path with <c>.log</c> appended.
    /// </summary>
    /// <param name="binaryPath">The <c>leanvm-sidecar</c> executable.</param>
    /// <param name="socketPath">The socket, in a directory only this user can write to.</param>
    /// <param name="threads">The sidecar's thread cap; 0 means one per core.</param>
    /// <exception cref="LeanPqException">The sidecar could not start, or one already listens there.</exception>
    public static Sidecar Start(string binaryPath, string socketPath, int threads = 0)
    {
        ArgumentNullException.ThrowIfNull(binaryPath);
        ArgumentNullException.ThrowIfNull(socketPath);
        ArgumentOutOfRangeException.ThrowIfNegative(threads);
        byte[] binary = Native.PathBytes(binaryPath);
        byte[] path = Native.PathBytes(socketPath);
        fixed (byte* binaryPointer = binary)
        fixed (byte* pathPointer = path)
        {
            int status = Native.SidecarStart(binaryPointer, (nuint)binary.Length, pathPointer, (nuint)path.Length, (nuint)threads, out SidecarHandle handle);
            return new(Native.Created(status, handle));
        }
    }

    /// <summary>The prover the sidecar runs: <c>"experimental"</c> or <c>"stable"</c>, which make the same proofs.</summary>
    public string GetProver() => Encoding.UTF8.GetString(Native.Take(Native.SidecarProver(_handle, out Native.Buffer buffer), buffer));

    /// <summary>
    /// Proves the union of the children's claims and the raw signatures' claims. Raw signatures are
    /// verified first; at most 16 children are accepted, and the input must not be empty.
    /// </summary>
    /// <param name="children">Aggregates to fold in; they stay owned by the caller.</param>
    /// <param name="xmss">leanXMSS signatures, each 2404 bytes.</param>
    /// <param name="sphincs">leanSPHINCS signatures, each 7740 bytes.</param>
    /// <exception cref="ArgumentException">A signature has the wrong length.</exception>
    /// <exception cref="LeanPqException">A signature does not verify, or the sidecar failed.</exception>
    public Aggregate Aggregate(IReadOnlyList<Aggregate> children, IReadOnlyList<SignedMessage> xmss, IReadOnlyList<SignedMessage> sphincs)
    {
        ArgumentNullException.ThrowIfNull(children);
        byte[] xmssRecords = SignedRecords(xmss, LeanPq.XmssSignatureLength, "leanXMSS");
        byte[] sphincsRecords = SignedRecords(sphincs, LeanPq.SphincsSignatureLength, "leanSPHINCS");
        // The native side rejects more than 16 children; checking first bounds the stackalloc.
        if (children.Count > MaxChildren)
        {
            throw new LeanPqException($"an aggregate takes at most {MaxChildren} children, got {children.Count}");
        }

        AggregateHandle[] handles = new AggregateHandle[children.Count];
        Span<nint> pointers = stackalloc nint[handles.Length];
        int borrowed = 0;
        try
        {
            for (; borrowed < handles.Length; borrowed++)
            {
                AggregateHandle child = (children[borrowed] ?? throw new ArgumentNullException(nameof(children), "a child is null")).Handle;
                bool added = false;
                child.DangerousAddRef(ref added);
                handles[borrowed] = child;
                pointers[borrowed] = child.DangerousGetHandle();
            }

            fixed (nint* childPointers = pointers)
            fixed (byte* xmssPointer = xmssRecords)
            fixed (byte* sphincsPointer = sphincsRecords)
            {
                // The counts come from the packed records, not from the lists, whose sizes may have changed.
                int status = Native.SidecarAggregate(
                    _handle,
                    childPointers, (nuint)handles.Length,
                    xmssPointer, (nuint)(xmssRecords.Length / (Native.ClaimLength + LeanPq.XmssSignatureLength)),
                    sphincsPointer, (nuint)(sphincsRecords.Length / (Native.ClaimLength + LeanPq.SphincsSignatureLength)),
                    out AggregateHandle handle);
                return new(Native.Created(status, handle));
            }
        }
        finally
        {
            for (int index = borrowed - 1; index >= 0; index--)
            {
                handles[index].DangerousRelease();
            }
        }
    }

    /// <summary>
    /// Verifies that <paramref name="proof"/>, from <see cref="Ethereum.LeanPq.Aggregate.ToBytes"/>, proves
    /// exactly the given claims, in any order; a repeated claim counts once.
    /// </summary>
    /// <exception cref="LeanPqException">The bytes are not a proof of exactly these claims.</exception>
    public Aggregate Verify(ReadOnlySpan<byte> proof, IReadOnlyList<SignatureClaim> xmssClaims, IReadOnlyList<SignatureClaim> sphincsClaims)
    {
        byte[] xmssRecords = ClaimRecords(xmssClaims);
        byte[] sphincsRecords = ClaimRecords(sphincsClaims);
        fixed (byte* proofPointer = proof)
        fixed (byte* xmssPointer = xmssRecords)
        fixed (byte* sphincsPointer = sphincsRecords)
        {
            int status = Native.SidecarVerify(
                _handle,
                proofPointer, (nuint)proof.Length,
                xmssPointer, (nuint)(xmssRecords.Length / Native.ClaimLength),
                sphincsPointer, (nuint)(sphincsRecords.Length / Native.ClaimLength),
                out AggregateHandle handle);
            return new(Native.Created(status, handle));
        }
    }

    /// <summary>
    /// Stops a sidecar <see cref="Start"/> launched at once, failing calls in progress, and closes the
    /// connection; the handle is freed once those calls return. Later calls throw
    /// <see cref="ObjectDisposedException"/>. A started sidecar that is never disposed is stopped when
    /// it is finalized.
    /// </summary>
    public void Dispose()
    {
        try
        {
            // Destroying the handle closes it too, so a failed close is not reported.
            _ = Native.SidecarClose(_handle);
        }
        catch (ObjectDisposedException)
        {
        }
        _handle.Dispose();
    }

    private static byte[] SignedRecords(IReadOnlyList<SignedMessage> entries, int signatureLength, string scheme)
    {
        ArgumentNullException.ThrowIfNull(entries);
        int recordLength = Native.ClaimLength + signatureLength;
        byte[] records = new byte[checked(entries.Count * recordLength)];
        for (int index = 0; index < entries.Count; index++)
        {
            SignedMessage entry = entries[index] ?? throw new ArgumentNullException(nameof(entries), "a signed message is null");
            entry.WriteRecord(records.AsSpan(index * recordLength, recordLength), signatureLength, scheme);
        }
        return records;
    }

    private static byte[] ClaimRecords(IReadOnlyList<SignatureClaim> claims)
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
}
