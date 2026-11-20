package org.ethereum.leanpq;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.lang.foreign.Arena;
import java.lang.foreign.FunctionDescriptor;
import java.lang.foreign.Linker;
import java.lang.foreign.MemoryLayout;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.SymbolLookup;
import java.lang.foreign.ValueLayout;
import java.lang.invoke.MethodHandle;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;
import java.util.Objects;

/** All FFM interaction is confined here; public binding classes never expose native addresses. */
final class Native {
    static final int PUBLIC_KEY_LENGTH = 32;
    static final int MESSAGE_LENGTH = 32;
    static final int CLAIM_LENGTH = PUBLIC_KEY_LENGTH + MESSAGE_LENGTH;
    static final int SEED_LENGTH = 32;
    static final int XMSS_SIGNATURE_LENGTH = 2404;
    static final int SPHINCS_SIGNATURE_LENGTH = 7740;
    static final int VRF_ROOT_LENGTH = 32;

    private static final int OK = 0;
    private static final int CHECKED_ERROR = 1;
    private static final long U32_MAX = 0xffff_ffffL;
    private static final ValueLayout.OfLong SIZE = ValueLayout.JAVA_LONG;
    private static final MemoryLayout BUFFER = MemoryLayout.structLayout(ValueLayout.ADDRESS, SIZE);
    private static final Linker LINKER = Linker.nativeLinker();
    private static final Arena LIBRARY_ARENA = Arena.ofShared();
    private static final String NATIVE_PATH_PROPERTY = "lean.pq.native.path";
    private static final Charset FILE_NAME_CHARSET = Charset.forName(System.getProperty("sun.jnu.encoding", "UTF-8"));
    private static final SymbolLookup LIBRARY = loadLibrary();

    private static final FunctionDescriptor HANDLE_TO_BUFFER = FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.ADDRESS);
    private static final FunctionDescriptor BYTES_TO_HANDLE = FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS);
    private static final FunctionDescriptor DESTROY = FunctionDescriptor.ofVoid(ValueLayout.ADDRESS);
    private static final FunctionDescriptor VERIFY = FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE);

    private static final MethodHandle LAST_ERROR = downcall("lpq_last_error", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle BUFFER_FREE = downcall("lpq_buffer_free", FunctionDescriptor.ofVoid(ValueLayout.ADDRESS, SIZE));

    private static final MethodHandle XMSS_GENERATE = downcall("lpq_xmss_secret_key_generate", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle XMSS_FROM_BYTES = downcall("lpq_xmss_secret_key_from_bytes", BYTES_TO_HANDLE);
    private static final MethodHandle XMSS_TO_BYTES = downcall("lpq_xmss_secret_key_to_bytes", HANDLE_TO_BUFFER);
    private static final MethodHandle XMSS_CACHE_TO_BYTES = downcall("lpq_xmss_secret_key_cache_to_bytes", HANDLE_TO_BUFFER);
    private static final MethodHandle XMSS_FROM_CACHE_BYTES = downcall("lpq_xmss_secret_key_from_cache_bytes", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle XMSS_PUBLIC_KEY = downcall("lpq_xmss_secret_key_public_key", HANDLE_TO_BUFFER);
    private static final MethodHandle XMSS_PREPARE = downcall("lpq_xmss_secret_key_prepare", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.JAVA_INT));
    private static final MethodHandle XMSS_SIGN = downcall("lpq_xmss_secret_key_sign", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.ADDRESS, SIZE, ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle XMSS_DESTROY = downcall("lpq_xmss_secret_key_destroy", DESTROY);
    private static final MethodHandle XMSS_VERIFY = downcall("lpq_xmss_verify", VERIFY);

    private static final MethodHandle SPHINCS_GENERATE = downcall("lpq_sphincs_secret_key_generate", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle SPHINCS_FROM_SEED = downcall("lpq_sphincs_secret_key_from_seed", BYTES_TO_HANDLE);
    private static final MethodHandle SPHINCS_FROM_BYTES = downcall("lpq_sphincs_secret_key_from_bytes", BYTES_TO_HANDLE);
    private static final MethodHandle SPHINCS_TO_BYTES = downcall("lpq_sphincs_secret_key_to_bytes", HANDLE_TO_BUFFER);
    private static final MethodHandle SPHINCS_PUBLIC_KEY = downcall("lpq_sphincs_secret_key_public_key", HANDLE_TO_BUFFER);
    private static final MethodHandle SPHINCS_SIGN = downcall("lpq_sphincs_secret_key_sign", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle SPHINCS_DESTROY = downcall("lpq_sphincs_secret_key_destroy", DESTROY);
    private static final MethodHandle SPHINCS_VERIFY = downcall("lpq_sphincs_verify", VERIFY);

    private static final MethodHandle SIDECAR_CONNECT = downcall("lpq_sidecar_connect", BYTES_TO_HANDLE);
    private static final MethodHandle SIDECAR_START = downcall("lpq_sidecar_start", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle SIDECAR_PROVER = downcall("lpq_sidecar_prover", HANDLE_TO_BUFFER);
    private static final MethodHandle SIDECAR_CLOSE = downcall("lpq_sidecar_close", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle SIDECAR_DESTROY = downcall("lpq_sidecar_destroy", DESTROY);

    private static final MethodHandle SIDECAR_AGGREGATE = downcall("lpq_sidecar_aggregate", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle SIDECAR_VERIFY = downcall("lpq_sidecar_verify", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle AGGREGATE_TO_BYTES = downcall("lpq_aggregate_to_bytes", HANDLE_TO_BUFFER);
    private static final MethodHandle AGGREGATE_XMSS_CLAIMS = downcall("lpq_aggregate_xmss_claims", HANDLE_TO_BUFFER);
    private static final MethodHandle AGGREGATE_SPHINCS_CLAIMS = downcall("lpq_aggregate_sphincs_claims", HANDLE_TO_BUFFER);
    private static final MethodHandle AGGREGATE_DESTROY = downcall("lpq_aggregate_destroy", DESTROY);

    private static final MethodHandle VRF_KEY_NEW = downcall("lpq_vrf_key_new", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.JAVA_INT, ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle VRF_KEY_FROM_CACHE_BYTES = downcall("lpq_vrf_key_from_cache_bytes", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS, SIZE, ValueLayout.ADDRESS));
    private static final MethodHandle VRF_KEY_CACHE_TO_BYTES = downcall("lpq_vrf_key_cache_to_bytes", HANDLE_TO_BUFFER);
    private static final MethodHandle VRF_KEY_ROOT = downcall("lpq_vrf_key_root", HANDLE_TO_BUFFER);
    private static final MethodHandle VRF_KEY_PROOF = downcall("lpq_vrf_key_proof", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, ValueLayout.JAVA_INT, ValueLayout.ADDRESS));
    private static final MethodHandle VRF_KEY_DESTROY = downcall("lpq_vrf_key_destroy", DESTROY);
    private static final MethodHandle VRF_VERIFY = downcall("lpq_vrf_verify", FunctionDescriptor.of(ValueLayout.JAVA_INT, ValueLayout.ADDRESS, SIZE, ValueLayout.JAVA_LONG, ValueLayout.ADDRESS, SIZE));

    private Native() {}

    /** Returns {@code bytes} after checking it is non-null and exactly {@code length} bytes long. */
    static byte[] requireLength(byte[] bytes, int length, String name) {
        Objects.requireNonNull(bytes, name);
        if (bytes.length != length) {
            throw new IllegalArgumentException(name + " must be exactly " + length + " bytes, got " + bytes.length);
        }
        return bytes;
    }

    static MemorySegment xmssGenerate() {
        return handle(XMSS_GENERATE);
    }

    static MemorySegment xmssFromBytes(byte[] bytes) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(XMSS_FROM_BYTES, copy(arena, bytes), (long) bytes.length);
        }
    }

    static byte[] xmssToBytes(MemorySegment key) {
        return buffer(XMSS_TO_BYTES, key);
    }

    static byte[] xmssCacheToBytes(MemorySegment key) {
        return buffer(XMSS_CACHE_TO_BYTES, key);
    }

    static MemorySegment xmssFromCacheBytes(byte[] seed, byte[] publicKey, byte[] cache) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(XMSS_FROM_CACHE_BYTES,
                copy(arena, seed), (long) seed.length,
                copy(arena, publicKey), (long) publicKey.length,
                copy(arena, cache), (long) cache.length);
        }
    }

    static byte[] xmssPublicKey(MemorySegment key) {
        return buffer(XMSS_PUBLIC_KEY, key);
    }

    static void xmssPrepare(MemorySegment key, long leafIndex) {
        check(status(XMSS_PREPARE, key, u32(leafIndex, "leafIndex")));
    }

    static byte[] xmssSign(MemorySegment key, byte[] message, long leafIndex) {
        int leaf = u32(leafIndex, "leafIndex");
        try (Arena arena = Arena.ofConfined()) {
            return buffer(XMSS_SIGN, key, copy(arena, message), (long) message.length, leaf);
        }
    }

    static boolean xmssVerify(byte[] publicKey, byte[] message, byte[] signature) {
        return verify(XMSS_VERIFY, publicKey, message, signature);
    }

    static void destroyXmss(MemorySegment pointer) {
        invoke(XMSS_DESTROY, pointer);
    }

    static MemorySegment sphincsGenerate() {
        return handle(SPHINCS_GENERATE);
    }

    static MemorySegment sphincsFromSeed(byte[] seed) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(SPHINCS_FROM_SEED, copy(arena, seed), (long) seed.length);
        }
    }

    static MemorySegment sphincsFromBytes(byte[] bytes) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(SPHINCS_FROM_BYTES, copy(arena, bytes), (long) bytes.length);
        }
    }

    static byte[] sphincsToBytes(MemorySegment key) {
        return buffer(SPHINCS_TO_BYTES, key);
    }

    static byte[] sphincsPublicKey(MemorySegment key) {
        return buffer(SPHINCS_PUBLIC_KEY, key);
    }

    static byte[] sphincsSign(MemorySegment key, byte[] message) {
        try (Arena arena = Arena.ofConfined()) {
            return buffer(SPHINCS_SIGN, key, copy(arena, message), (long) message.length);
        }
    }

    static boolean sphincsVerify(byte[] publicKey, byte[] message, byte[] signature) {
        return verify(SPHINCS_VERIFY, publicKey, message, signature);
    }

    static void destroySphincs(MemorySegment pointer) {
        invoke(SPHINCS_DESTROY, pointer);
    }

    static MemorySegment sidecarConnect(Path socket) {
        byte[] path = pathBytes(socket);
        try (Arena arena = Arena.ofConfined()) {
            return handle(SIDECAR_CONNECT, copy(arena, path), (long) path.length);
        }
    }

    static MemorySegment sidecarStart(Path binary, Path socket, int threads) {
        byte[] binaryPath = pathBytes(binary);
        byte[] socketPath = pathBytes(socket);
        try (Arena arena = Arena.ofConfined()) {
            return handle(SIDECAR_START,
                copy(arena, binaryPath), (long) binaryPath.length,
                copy(arena, socketPath), (long) socketPath.length,
                (long) threads);
        }
    }

    static String sidecarProver(MemorySegment sidecar) {
        return new String(buffer(SIDECAR_PROVER, sidecar), StandardCharsets.UTF_8);
    }

    static void closeSidecar(MemorySegment sidecar) {
        check(status(SIDECAR_CLOSE, sidecar));
    }

    static void destroySidecar(MemorySegment pointer) {
        invoke(SIDECAR_DESTROY, pointer);
    }

    /** Records are concatenated {@code pk|msg|sig} entries of the scheme's fixed record width. */
    static MemorySegment sidecarAggregate(MemorySegment sidecar, List<MemorySegment> children, byte[] xmss, long xmssCount, byte[] sphincs, long sphincsCount) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(SIDECAR_AGGREGATE, sidecar,
                pointerArray(arena, children), (long) children.size(),
                copy(arena, xmss), xmssCount,
                copy(arena, sphincs), sphincsCount);
        }
    }

    /** Claims are concatenated 64-byte {@code pk|msg} records. */
    static MemorySegment sidecarVerify(MemorySegment sidecar, byte[] bytes, byte[] xmssClaims, long xmssCount, byte[] sphincsClaims, long sphincsCount) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(SIDECAR_VERIFY, sidecar,
                copy(arena, bytes), (long) bytes.length,
                copy(arena, xmssClaims), xmssCount,
                copy(arena, sphincsClaims), sphincsCount);
        }
    }

    static byte[] aggregateToBytes(MemorySegment aggregate) {
        return buffer(AGGREGATE_TO_BYTES, aggregate);
    }

    /** Returns concatenated 64-byte {@code pk|msg} records. */
    static byte[] xmssClaims(MemorySegment aggregate) {
        return buffer(AGGREGATE_XMSS_CLAIMS, aggregate);
    }

    /** Returns concatenated 64-byte {@code pk|msg} records. */
    static byte[] sphincsClaims(MemorySegment aggregate) {
        return buffer(AGGREGATE_SPHINCS_CLAIMS, aggregate);
    }

    static void destroyAggregate(MemorySegment pointer) {
        invoke(AGGREGATE_DESTROY, pointer);
    }

    static MemorySegment vrfKeyNew(byte[] seed, long start, long end) {
        int first = u32(start, "start");
        int last = u32(end, "end");
        try (Arena arena = Arena.ofConfined()) {
            return handle(VRF_KEY_NEW, copy(arena, seed), (long) seed.length, first, last);
        }
    }

    static MemorySegment vrfKeyFromCacheBytes(byte[] seed, byte[] root, byte[] cache) {
        try (Arena arena = Arena.ofConfined()) {
            return handle(VRF_KEY_FROM_CACHE_BYTES, copy(arena, seed), (long) seed.length, copy(arena, root), (long) root.length, copy(arena, cache), (long) cache.length);
        }
    }

    static byte[] vrfCacheToBytes(MemorySegment key) {
        return buffer(VRF_KEY_CACHE_TO_BYTES, key);
    }

    static byte[] vrfRoot(MemorySegment key) {
        return buffer(VRF_KEY_ROOT, key);
    }

    static byte[] vrfProof(MemorySegment key, long slot) {
        return buffer(VRF_KEY_PROOF, key, u32(slot, "slot"));
    }

    static void destroyVrfKey(MemorySegment pointer) {
        invoke(VRF_KEY_DESTROY, pointer);
    }

    /** The slot is passed as an unsigned 64-bit integer. */
    static boolean vrfVerify(byte[] root, long slot, byte[] proof) {
        try (Arena arena = Arena.ofConfined()) {
            return verified(status(VRF_VERIFY,
                copy(arena, root), (long) root.length,
                slot,
                copy(arena, proof), (long) proof.length));
        }
    }

    /**
     * Loads {@code -Dlean.pq.native.path} when set; otherwise extracts the library bundled in this jar
     * for the current platform and loads it: from a private temporary directory on Linux and macOS,
     * from a per-user cache on Windows.
     */
    private static SymbolLookup loadLibrary() {
        String override = System.getProperty(NATIVE_PATH_PROPERTY);
        if (override != null && !override.isBlank()) {
            return SymbolLookup.libraryLookup(Path.of(override).toAbsolutePath(), LIBRARY_ARENA);
        }
        String platform = bundledPlatform();
        String library = switch (platform) {
            case "macos-universal" -> "liblean_pq_native.dylib";
            case "windows-x86_64" -> "lean_pq_native.dll";
            default -> "liblean_pq_native.so";
        };
        try (InputStream bundled = Native.class.getResourceAsStream("native/" + platform + "/" + library)) {
            if (bundled == null) {
                throw new IllegalStateException("this lean-pq jar bundles no native library for " + platform
                    + "; set -D" + NATIVE_PATH_PROPERTY + " to a lean-pq native library built for this platform");
            }
            if (platform.equals("windows-x86_64")) {
                return lookupBundled(cachedLibrary(bundled.readAllBytes(), library), platform);
            }
            // createTempDirectory makes an owner-only directory on POSIX file systems.
            Path directory = Files.createTempDirectory("lean-pq-");
            Path file = directory.resolve(library);
            try {
                Files.copy(bundled, file);
                return lookupBundled(file, platform);
            } finally {
                // The loaded library stays mapped after its file is removed, so nothing is left behind.
                Files.deleteIfExists(file);
                Files.deleteIfExists(directory);
            }
        } catch (IOException error) {
            throw new UncheckedIOException("could not extract the bundled lean-pq native library", error);
        }
    }

    private static SymbolLookup lookupBundled(Path file, String platform) {
        try {
            return SymbolLookup.libraryLookup(file, LIBRARY_ARENA);
        } catch (IllegalArgumentException error) {
            throw new IllegalStateException("could not load the bundled lean-pq native library for " + platform
                + " (Linux builds need glibc 2.17 or newer); set -D" + NATIVE_PATH_PROPERTY
                + " to a lean-pq native library built for this system", error);
        }
    }

    /**
     * Windows cannot delete a loaded DLL, so the library is installed once per distinct build as
     * {@code %LOCALAPPDATA%\lean-pq\native\<SHA-256 of the library>\<library>} and reused by every
     * later JVM. An existing copy is used only if its bytes equal the bundled library; otherwise a
     * fresh copy is written beside it and moved into place atomically.
     */
    private static Path cachedLibrary(byte[] bytes, String library) throws IOException {
        String digest;
        try {
            digest = HexFormat.of().formatHex(MessageDigest.getInstance("SHA-256").digest(bytes));
        } catch (NoSuchAlgorithmException error) {
            throw new IllegalStateException("SHA-256 is unavailable", error);
        }
        String localAppData = System.getenv("LOCALAPPDATA");
        Path root = localAppData != null && !localAppData.isBlank()
            ? Path.of(localAppData)
            : Path.of(System.getProperty("user.home"), "AppData", "Local");
        Path directory = root.resolve("lean-pq").resolve("native").resolve(digest);
        Path file = directory.resolve(library);
        if (hasContent(file, bytes)) {
            return file;
        }
        Files.createDirectories(directory);
        Path partial = Files.createTempFile(directory, library, ".partial");
        try {
            Files.write(partial, bytes);
            try {
                Files.move(partial, file, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
            } catch (IOException error) {
                // Another JVM may have installed the same library meanwhile and now holds it loaded.
                if (!hasContent(file, bytes)) {
                    throw error;
                }
            }
        } finally {
            Files.deleteIfExists(partial);
        }
        return file;
    }

    private static boolean hasContent(Path file, byte[] bytes) throws IOException {
        return Files.isRegularFile(file) && Files.size(file) == bytes.length && Arrays.equals(Files.readAllBytes(file), bytes);
    }

    /** Names the jar's native resource directory for this JVM's platform. */
    private static String bundledPlatform() {
        String os = System.getProperty("os.name", "");
        String arch = System.getProperty("os.arch", "");
        boolean x86_64 = arch.equals("amd64") || arch.equals("x86_64");
        if (os.startsWith("Mac OS X")) {
            // One universal library carries both the x86_64 and arm64 slices.
            return "macos-universal";
        }
        if (os.equals("Linux") && x86_64) {
            return "linux-x86_64";
        }
        if (os.equals("Linux") && arch.equals("aarch64")) {
            return "linux-aarch64";
        }
        if (os.startsWith("Windows") && x86_64) {
            return "windows-x86_64";
        }
        throw new IllegalStateException("lean-pq bundles native libraries for Linux x86_64 and aarch64 (glibc), macOS"
            + " (x86_64 and arm64) and Windows x86_64, not " + os + " " + arch + "; set -D" + NATIVE_PATH_PROPERTY
            + " to a lean-pq native library built for this platform");
    }

    private static MethodHandle downcall(String name, FunctionDescriptor descriptor) {
        MemorySegment symbol = LIBRARY.find(name).orElseThrow(() -> new IllegalStateException("missing native symbol " + name));
        return LINKER.downcallHandle(symbol, descriptor);
    }

    private static boolean verify(MethodHandle function, byte[] publicKey, byte[] message, byte[] signature) {
        try (Arena arena = Arena.ofConfined()) {
            return verified(status(function,
                copy(arena, publicKey), (long) publicKey.length,
                copy(arena, message), (long) message.length,
                copy(arena, signature), (long) signature.length));
        }
    }

    private static boolean verified(int status) {
        if (status == CHECKED_ERROR) {
            return false;
        }
        check(status);
        return true;
    }

    private static MemorySegment handle(MethodHandle function, Object... arguments) {
        try (Arena arena = Arena.ofConfined()) {
            MemorySegment out = arena.allocate(ValueLayout.ADDRESS);
            Object[] all = Arrays.copyOf(arguments, arguments.length + 1);
            all[arguments.length] = out;
            check(status(function, all));
            MemorySegment result = out.get(ValueLayout.ADDRESS, 0);
            if (result.address() == 0) {
                throw new LeanPqException("native operation returned a null handle");
            }
            return MemorySegment.ofAddress(result.address());
        }
    }

    private static byte[] buffer(MethodHandle function, Object... arguments) {
        try (Arena arena = Arena.ofConfined()) {
            MemorySegment out = arena.allocate(BUFFER);
            Object[] all = Arrays.copyOf(arguments, arguments.length + 1);
            all[arguments.length] = out;
            check(status(function, all));
            MemorySegment data = out.get(ValueLayout.ADDRESS, 0);
            long length = out.get(SIZE, ValueLayout.ADDRESS.byteSize());
            try {
                if (length < 0 || length > Integer.MAX_VALUE) {
                    throw new LeanPqException("native buffer length is invalid: " + length);
                }
                return length == 0 ? new byte[0] : data.reinterpret(length).toArray(ValueLayout.JAVA_BYTE);
            } finally {
                invoke(BUFFER_FREE, data, length);
            }
        }
    }

    private static int status(MethodHandle function, Object... arguments) {
        return (int) invoke(function, arguments);
    }

    private static Object invoke(MethodHandle function, Object... arguments) {
        try {
            return function.invokeWithArguments(arguments);
        } catch (RuntimeException error) {
            throw error;
        } catch (Throwable error) {
            throw new IllegalStateException("FFM invocation failed", error);
        }
    }

    private static void check(int status) {
        if (status != OK) {
            throw new LeanPqException(errorMessage());
        }
    }

    private static String errorMessage() {
        String message = new String(buffer(LAST_ERROR), StandardCharsets.UTF_8);
        return message.isBlank() ? "native lean-pq operation failed" : message;
    }

    /** Encodes a path as the platform encodes file names, which is how the native side reads it. */
    private static byte[] pathBytes(Path path) {
        return path.toString().getBytes(FILE_NAME_CHARSET);
    }

    private static MemorySegment copy(Arena arena, byte[] bytes) {
        if (bytes.length == 0) {
            return MemorySegment.NULL;
        }
        MemorySegment copy = arena.allocate(bytes.length, 1);
        MemorySegment.copy(bytes, 0, copy, ValueLayout.JAVA_BYTE, 0, bytes.length);
        return copy;
    }

    private static MemorySegment pointerArray(Arena arena, List<MemorySegment> pointers) {
        if (pointers.isEmpty()) {
            return MemorySegment.NULL;
        }
        MemorySegment result = arena.allocate(ValueLayout.ADDRESS, pointers.size());
        for (int index = 0; index < pointers.size(); index++) {
            result.setAtIndex(ValueLayout.ADDRESS, index, pointers.get(index));
        }
        return result;
    }

    private static int u32(long value, String name) {
        if (value < 0 || value > U32_MAX) {
            throw new IllegalArgumentException(name + " must fit an unsigned 32-bit integer");
        }
        return (int) value;
    }
}
