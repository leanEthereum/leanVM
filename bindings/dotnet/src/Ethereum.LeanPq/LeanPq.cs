namespace Ethereum.LeanPq;

/// <summary>Verifies single signatures and VRF proofs; <see cref="Sidecar"/> aggregates signatures.</summary>
public static class LeanPq
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

    /// <summary>Returns whether the 2404-byte leanXMSS signature is valid for the public key and message.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public static bool XmssVerify(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message, ReadOnlySpan<byte> signature)
    {
        Native.RequireLength(publicKey, PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, MessageLength, nameof(message));
        return Native.XmssVerify(publicKey, message, signature);
    }

    /// <summary>Returns whether the 7740-byte leanSPHINCS signature is valid for the public key and message.</summary>
    /// <exception cref="ArgumentException">The public key or message is not 32 bytes.</exception>
    public static bool SphincsVerify(ReadOnlySpan<byte> publicKey, ReadOnlySpan<byte> message, ReadOnlySpan<byte> signature)
    {
        Native.RequireLength(publicKey, PublicKeyLength, nameof(publicKey));
        Native.RequireLength(message, MessageLength, nameof(message));
        return Native.SphincsVerify(publicKey, message, signature);
    }

    /// <summary>
    /// Returns whether a 1024-byte VRF proof opens the slot under a 32-byte root, as <c>is_valid_vrf_proof</c>.
    /// </summary>
    /// <exception cref="ArgumentException">The root is not 32 bytes.</exception>
    public static bool VrfVerify(ReadOnlySpan<byte> root, ulong slot, ReadOnlySpan<byte> proof)
    {
        Native.RequireLength(root, VrfRootLength, nameof(root));
        return Native.VrfVerify(root, slot, proof);
    }
}
