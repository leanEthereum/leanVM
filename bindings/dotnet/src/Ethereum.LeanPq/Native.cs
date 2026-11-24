using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

namespace Ethereum.PostQuantum;

/// <summary>All P/Invoke is confined here; public types never expose native addresses.</summary>
internal static unsafe partial class Native
{
    internal const int ClaimLength = LeanPq.PublicKeyLength + LeanPq.MessageLength;
    private const string NativePathVariable = "LEAN_PQ_NATIVE_PATH";

    private const string Library = "lean_pq_native";
    private const int Ok = 0;
    private const int CheckedError = 1;

    [StructLayout(LayoutKind.Sequential)]
    internal struct Buffer
    {
        public byte* Data;
        public nuint Length;
    }

#pragma warning disable CA2255 // The resolver must be registered before the first P/Invoke.
    [ModuleInitializer]
#pragma warning restore CA2255
    internal static void RegisterResolver() =>
        NativeLibrary.SetDllImportResolver(typeof(Native).Assembly, Resolve);

    /// <summary>
    /// Loads <c>LEAN_PQ_NATIVE_PATH</c> when set; otherwise the runtime probes as usual, finding the
    /// package's <c>runtimes/&lt;rid&gt;/native</c> library.
    /// </summary>
    private static nint Resolve(string name, Assembly assembly, DllImportSearchPath? searchPath)
    {
        if (name != Library)
        {
            return 0;
        }
        string? path = Environment.GetEnvironmentVariable(NativePathVariable);
        return string.IsNullOrEmpty(path) ? 0 : NativeLibrary.Load(Path.GetFullPath(path));
    }

    [LibraryImport(Library, EntryPoint = "lpq_last_error")]
    private static partial int LastError(out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_buffer_free")]
    private static partial void BufferFree(byte* data, nuint length);

    [LibraryImport(Library, EntryPoint = "lpq_setup")]
    internal static partial int Setup(nuint threads);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_generate")]
    internal static partial int XmssGenerate(out XmssKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_from_bytes")]
    internal static partial int XmssFromBytes(byte* data, nuint length, out XmssKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_to_bytes")]
    internal static partial int XmssToBytes(XmssKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_cache_to_bytes")]
    internal static partial int XmssCacheToBytes(XmssKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_from_cache_bytes")]
    internal static partial int XmssFromCacheBytes(
        byte* seed, nuint seedLength, byte* publicKey, nuint publicKeyLength, byte* cache, nuint cacheLength, out XmssKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_public_key")]
    internal static partial int XmssPublicKey(XmssKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_prepare")]
    internal static partial int XmssPrepare(XmssKeyHandle key, uint leafIndex);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_sign")]
    internal static partial int XmssSign(XmssKeyHandle key, byte* message, nuint messageLength, uint leafIndex, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_secret_key_destroy")]
    internal static partial void XmssDestroy(nint key);

    [LibraryImport(Library, EntryPoint = "lpq_xmss_verify")]
    internal static partial int XmssVerify(byte* publicKey, nuint publicKeyLength, byte* message, nuint messageLength, byte* signature, nuint signatureLength);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_generate")]
    internal static partial int SphincsGenerate(out SphincsKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_from_seed")]
    internal static partial int SphincsFromSeed(byte* seed, nuint seedLength, out SphincsKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_from_bytes")]
    internal static partial int SphincsFromBytes(byte* data, nuint length, out SphincsKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_to_bytes")]
    internal static partial int SphincsToBytes(SphincsKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_public_key")]
    internal static partial int SphincsPublicKey(SphincsKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_sign")]
    internal static partial int SphincsSign(SphincsKeyHandle key, byte* message, nuint messageLength, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_secret_key_destroy")]
    internal static partial void SphincsDestroy(nint key);

    [LibraryImport(Library, EntryPoint = "lpq_sphincs_verify")]
    internal static partial int SphincsVerify(byte* publicKey, nuint publicKeyLength, byte* message, nuint messageLength, byte* signature, nuint signatureLength);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_create")]
    internal static partial int AggregateCreate(
        nint* children, nuint childCount, byte* xmss, nuint xmssCount, byte* sphincs, nuint sphincsCount, out AggregateHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_create_only")]
    internal static partial int AggregateCreateOnly(
        nint* children, nuint childCount, byte* xmss, nuint xmssCount, byte* sphincs, nuint sphincsCount,
        byte* xmssClaims, nuint xmssClaimCount, byte* sphincsClaims, nuint sphincsClaimCount, out AggregateHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_from_bytes")]
    internal static partial int AggregateFromBytes(
        byte* data, nuint length, byte* xmssClaims, nuint xmssCount, byte* sphincsClaims, nuint sphincsCount, out AggregateHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_to_bytes")]
    internal static partial int AggregateToBytes(AggregateHandle aggregate, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_xmss_claims")]
    internal static partial int AggregateXmssClaims(AggregateHandle aggregate, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_sphincs_claims")]
    internal static partial int AggregateSphincsClaims(AggregateHandle aggregate, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_aggregate_destroy")]
    internal static partial void AggregateDestroy(nint aggregate);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_new")]
    internal static partial int VrfKeyNew(byte* seed, nuint seedLength, uint start, uint end, out VrfKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_from_cache_bytes")]
    internal static partial int VrfKeyFromCacheBytes(
        byte* seed, nuint seedLength, byte* root, nuint rootLength, byte* cache, nuint cacheLength, out VrfKeyHandle output);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_cache_to_bytes")]
    internal static partial int VrfKeyCacheToBytes(VrfKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_root")]
    internal static partial int VrfKeyRoot(VrfKeyHandle key, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_proof")]
    internal static partial int VrfKeyProof(VrfKeyHandle key, uint slot, out Buffer output);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_key_destroy")]
    internal static partial void VrfKeyDestroy(nint key);

    [LibraryImport(Library, EntryPoint = "lpq_vrf_verify")]
    internal static partial int VrfVerify(byte* root, nuint rootLength, ulong slot, byte* proof, nuint proofLength);

    /// <summary>Throws <see cref="LeanPqException"/> with the native error unless <paramref name="status"/> is success.</summary>
    /// <remarks>
    /// The native error is thread-local; the runtime keeps a managed thread on one OS thread between
    /// the failed call and this read.
    /// </remarks>
    internal static void Check(int status)
    {
        if (status != Ok)
        {
            throw new LeanPqException(ErrorMessage());
        }
    }

    /// <summary>Copies a returned buffer into a managed array and frees it, after checking the call's status.</summary>
    internal static byte[] Take(int status, Buffer buffer)
    {
        Check(status);
        try
        {
            if (buffer.Length > (nuint)Array.MaxLength)
            {
                throw new LeanPqException($"native buffer length is invalid: {buffer.Length}");
            }
            return buffer.Length == 0 ? [] : new ReadOnlySpan<byte>(buffer.Data, (int)buffer.Length).ToArray();
        }
        finally
        {
            BufferFree(buffer.Data, buffer.Length);
        }
    }

    /// <summary>Returns the handle a call created, after checking the call's status.</summary>
    internal static T Created<T>(int status, T handle) where T : SafeHandle
    {
        if (status != Ok)
        {
            handle.Dispose();
            Check(status);
        }
        if (handle.IsInvalid)
        {
            handle.Dispose();
            throw new LeanPqException("native operation returned a null handle");
        }
        return handle;
    }

    internal static void RequireLength(ReadOnlySpan<byte> bytes, int length, string name)
    {
        if (bytes.Length != length)
        {
            throw new ArgumentException($"{name} must be exactly {length} bytes, got {bytes.Length}", name);
        }
    }

    /// <summary>A verify call's verdict: false for a checked error; a caught panic throws.</summary>
    internal static bool Verified(int status)
    {
        if (status == CheckedError)
        {
            return false;
        }
        Check(status);
        return true;
    }

    private static string ErrorMessage()
    {
        if (LastError(out Buffer buffer) != Ok)
        {
            return "native lean-pq operation failed";
        }
        string message = Encoding.UTF8.GetString(Take(Ok, buffer));
        return string.IsNullOrWhiteSpace(message) ? "native lean-pq operation failed" : message;
    }
}
