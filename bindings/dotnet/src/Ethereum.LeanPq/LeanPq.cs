namespace Ethereum.PostQuantum;

/// <summary>Verifies single signatures and VRF proofs, and aggregates signatures.</summary>
public static unsafe class LeanPq
{
    /// <summary>The length of a public key, in bytes.</summary>
    public const int PublicKeyLength = 32;

    /// <summary>The length of a signed message, in bytes.</summary>
    public const int MessageLength = 32;

    /// <summary>The length of a secret key's seed, in bytes.</summary>
    public const int SeedLength = 32;

    /// <summary>The length of a leanXMSS signature, in bytes.</summary>
    public const int XmssSignatureLength = 2404;

    /// <summary>The length of a leanSPHINCS signature, in bytes.</summary>
    public const int SphincsSignatureLength = 7740;

    /// <summary>The length of a VRF root, in bytes.</summary>
    public const int VrfRootLength = 32;

    /// <summary>The length of a VRF proof, in bytes.</summary>
    public const int VrfProofLength = 1024;

    /// <summary>The most children one aggregation takes.</summary>
    public const int MaxChildren = 16;

    /// <summary>
    /// Starts the prover with <paramref name="threads"/> threads (0: one per core), before the first
    /// aggregation.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException"><paramref name="threads"/> is negative.</exception>
    /// <exception cref="LeanPqException">
    /// <paramref name="threads"/> exceeds the machine's parallelism, or the prover already runs with another count.
    /// </exception>
    public static void Setup(int threads)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(threads);
        Native.Check(Native.Setup((nuint)threads));
    }

    /// <summary>Returns whether the 2404-byte leanXMSS signature is valid for the public key and message.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public static bool XmssVerify(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message, ReadOnlySpan<byte> signature)
    {
        Native.RequireLength(publicKey, PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, MessageLength, nameof(message));
        fixed (byte* publicKeyPointer = publicKey)
        fixed (byte* messagePointer = message)
        fixed (byte* signaturePointer = signature)
        {
            return Native.Verified(Native.XmssVerify(
                publicKeyPointer, (nuint)publicKey.Length,
                messagePointer, (nuint)message.Length,
                signaturePointer, (nuint)signature.Length));
        }
    }

    /// <summary>Returns whether the 7740-byte leanSPHINCS signature is valid for the public key and message.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public static bool SphincsVerify(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message, ReadOnlySpan<byte> signature)
    {
        Native.RequireLength(publicKey, PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, MessageLength, nameof(message));
        fixed (byte* publicKeyPointer = publicKey)
        fixed (byte* messagePointer = message)
        fixed (byte* signaturePointer = signature)
        {
            return Native.Verified(Native.SphincsVerify(
                publicKeyPointer, (nuint)publicKey.Length,
                messagePointer, (nuint)message.Length,
                signaturePointer, (nuint)signature.Length));
        }
    }

    /// <summary>
    /// Returns whether a 1024-byte VRF proof opens the slot under a 32-byte root, as <c>is_valid_vrf_proof</c>.
    /// </summary>
    /// <exception cref="ArgumentException">The root is not 32 bytes.</exception>
    public static bool VrfVerify(ReadOnlySpan<byte> root, ulong slot, ReadOnlySpan<byte> proof)
    {
        Native.RequireLength(root, VrfRootLength, nameof(root));
        fixed (byte* rootPointer = root)
        fixed (byte* proofPointer = proof)
        {
            return Native.Verified(Native.VrfVerify(rootPointer, (nuint)root.Length, slot, proofPointer, (nuint)proof.Length));
        }
    }

    /// <summary>
    /// Proves the union of the children's claims and the raw signatures' claims. Raw signatures are
    /// verified first; at most 16 children are accepted, and the input must not be empty.
    /// </summary>
    /// <param name="children">Aggregates to fold in; they stay owned by the caller.</param>
    /// <param name="xmss">leanXMSS signatures, each 2404 bytes.</param>
    /// <param name="sphincs">leanSPHINCS signatures, each 7740 bytes.</param>
    /// <exception cref="ArgumentException">A signature has the wrong length.</exception>
    /// <exception cref="LeanPqException">A signature does not verify, or proving failed.</exception>
    public static Aggregate Aggregate(IReadOnlyList<Aggregate> children, IReadOnlyList<SignedMessage> xmss, IReadOnlyList<SignedMessage> sphincs) =>
        Prove(children, xmss, sphincs, null, null);

    /// <summary>
    /// <see cref="Aggregate(IReadOnlyList{Ethereum.PostQuantum.Aggregate}, IReadOnlyList{SignedMessage}, IReadOnlyList{SignedMessage})"/>,
    /// but the result proves exactly the given claims, in any order, a repeat counting once; each must
    /// be one the inputs cover.
    /// </summary>
    /// <exception cref="ArgumentException">A signature has the wrong length.</exception>
    /// <exception cref="LeanPqException">A signature does not verify, a claim is not covered, or proving failed.</exception>
    public static Aggregate AggregateOnly(
        IReadOnlyList<Aggregate> children, IReadOnlyList<SignedMessage> xmss, IReadOnlyList<SignedMessage> sphincs,
        IReadOnlyList<SignatureClaim> xmssClaims, IReadOnlyList<SignatureClaim> sphincsClaims) =>
        Prove(children, xmss, sphincs, Ethereum.PostQuantum.Aggregate.ClaimRecords(xmssClaims), Ethereum.PostQuantum.Aggregate.ClaimRecords(sphincsClaims));

    /// <summary><paramref name="xmssClaims"/> and <paramref name="sphincsClaims"/> are both null to prove every covered claim.</summary>
    private static Aggregate Prove(
        IReadOnlyList<Aggregate> children, IReadOnlyList<SignedMessage> xmss, IReadOnlyList<SignedMessage> sphincs,
        byte[]? xmssClaims, byte[]? sphincsClaims)
    {
        ArgumentNullException.ThrowIfNull(children);
        byte[] xmssRecords = SignedRecords(xmss, XmssSignatureLength, "leanXMSS");
        byte[] sphincsRecords = SignedRecords(sphincs, SphincsSignatureLength, "leanSPHINCS");
        // The native side rejects more than 16 children; checking first bounds the stackalloc.
        int childCount = children.Count;
        if (childCount > MaxChildren)
        {
            throw new LeanPqException($"an aggregate takes at most {MaxChildren} children, got {childCount}");
        }

        AggregateHandle[] handles = new AggregateHandle[childCount];
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

            // The counts come from the packed records, not from the lists, whose sizes may have changed.
            nuint xmssCount = (nuint)(xmssRecords.Length / (Native.ClaimLength + XmssSignatureLength));
            nuint sphincsCount = (nuint)(sphincsRecords.Length / (Native.ClaimLength + SphincsSignatureLength));
            fixed (nint* childPointers = pointers)
            fixed (byte* xmssPointer = xmssRecords)
            fixed (byte* sphincsPointer = sphincsRecords)
            fixed (byte* xmssClaimPointer = xmssClaims)
            fixed (byte* sphincsClaimPointer = sphincsClaims)
            {
                AggregateHandle handle;
                int status = xmssClaims is null || sphincsClaims is null
                    ? Native.AggregateCreate(
                        childPointers, (nuint)handles.Length, xmssPointer, xmssCount, sphincsPointer, sphincsCount, out handle)
                    : Native.AggregateCreateOnly(
                        childPointers, (nuint)handles.Length, xmssPointer, xmssCount, sphincsPointer, sphincsCount,
                        xmssClaimPointer, (nuint)(xmssClaims.Length / Native.ClaimLength),
                        sphincsClaimPointer, (nuint)(sphincsClaims.Length / Native.ClaimLength),
                        out handle);
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
}
