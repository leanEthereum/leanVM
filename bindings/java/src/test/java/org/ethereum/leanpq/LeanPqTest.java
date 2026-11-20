package org.ethereum.leanpq;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;
import java.util.Set;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledOnOs;
import org.junit.jupiter.api.condition.EnabledOnOs;
import org.junit.jupiter.api.condition.OS;
import org.junit.jupiter.api.io.TempDir;

class LeanPqTest {
    private static final Set<String> PROVERS = Set.of("experimental", "stable");

    @Test
    void signsVerifiesAndRejectsAnotherMessage() {
        byte[] message = bytes(0x42);
        byte[] other = bytes(0x43);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(1));
             SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(bytes(2))) {
            byte[] xmssSignature = xmss.sign(message, 3);
            assertEquals(2404, xmssSignature.length);
            assertTrue(LeanPq.xmssVerify(xmss.publicKey(), message, xmssSignature));
            assertFalse(LeanPq.xmssVerify(xmss.publicKey(), other, xmssSignature));

            byte[] sphincsSignature = sphincs.sign(message);
            assertEquals(7740, sphincsSignature.length);
            assertTrue(LeanPq.sphincsVerify(sphincs.publicKey(), message, sphincsSignature));
            assertFalse(LeanPq.sphincsVerify(sphincs.publicKey(), other, sphincsSignature));
        }
    }

    @Test
    void secretKeysRoundTripThroughBytes() {
        byte[] message = bytes(7);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(3));
             XmssSecretKey restored = XmssSecretKey.fromBytes(xmss.toBytes())) {
            assertArrayEquals(xmss.publicKey(), restored.publicKey());
            assertTrue(LeanPq.xmssVerify(xmss.publicKey(), message, restored.sign(message, 9)));
        }
        try (SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(bytes(4));
             SphincsSecretKey restored = SphincsSecretKey.fromBytes(sphincs.toBytes())) {
            assertArrayEquals(bytes(4), sphincs.toBytes());
            assertArrayEquals(sphincs.publicKey(), restored.publicKey());
            assertTrue(LeanPq.sphincsVerify(sphincs.publicKey(), message, restored.sign(message)));
        }
    }

    @Test
    void xmssKeyLoadsFromItsTreeCache() {
        byte[] message = bytes(7);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(7))) {
            xmss.prepare(3);
            byte[] cache = xmss.cacheToBytes();
            byte[] publicKey = xmss.publicKey();
            try (XmssSecretKey loaded = XmssSecretKey.fromCacheBytes(bytes(7), publicKey, cache)) {
                assertArrayEquals(xmss.publicKey(), loaded.publicKey());
                assertArrayEquals(cache, loaded.cacheToBytes());
                byte[] signature = loaded.sign(message, 3);
                assertArrayEquals(xmss.sign(message, 3), signature);
                assertTrue(LeanPq.xmssVerify(xmss.publicKey(), message, signature));
            }
            byte[] truncated = Arrays.copyOf(cache, cache.length - 1);
            byte[] tampered = cache.clone();
            tampered[0] ^= 1;
            byte[] otherKey;
            try (XmssSecretKey other = XmssSecretKey.fromSeed(bytes(8))) {
                otherKey = other.publicKey();
            }
            assertThrows(LeanPqException.class, () -> XmssSecretKey.fromCacheBytes(bytes(7), publicKey, truncated));
            assertThrows(LeanPqException.class, () -> XmssSecretKey.fromCacheBytes(bytes(7), publicKey, tampered));
            assertThrows(LeanPqException.class, () -> XmssSecretKey.fromCacheBytes(bytes(7), otherKey, cache));
            assertThrows(IllegalArgumentException.class, () -> XmssSecretKey.fromCacheBytes(new byte[31], publicKey, cache));
        }
    }

    @Test
    void vrfMatchesThePinnedVector() {
        byte[] root = HexFormat.of().parseHex("c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45");
        try (VrfKey key = VrfKey.fromSeed(bytes(9), 100, 200)) {
            assertArrayEquals(root, key.root());
            byte[] proof = key.proof(150);
            assertEquals(1024, proof.length);
            assertTrue(LeanPq.vrfVerify(root, 150, proof));
            assertFalse(LeanPq.vrfVerify(root, 151, proof));
            assertFalse(LeanPq.vrfVerify(root, 150, Arrays.copyOf(proof, proof.length - 1)));
            for (long slot : new long[] {100, 199}) {
                assertTrue(LeanPq.vrfVerify(root, slot, key.proof(slot)));
            }
        }
    }

    @Test
    void vrfKeyLoadsFromItsCache() {
        byte[] root = HexFormat.of().parseHex("c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45");
        try (VrfKey key = VrfKey.fromSeed(bytes(9), 100, 200)) {
            byte[] cache = key.cacheToBytes();
            try (VrfKey loaded = VrfKey.fromCacheBytes(bytes(9), root, cache)) {
                assertArrayEquals(cache, loaded.cacheToBytes());
                assertTrue(LeanPq.vrfVerify(root, 150, loaded.proof(150)));
            }
            byte[] truncated = Arrays.copyOf(cache, cache.length - 1);
            assertThrows(LeanPqException.class, () -> VrfKey.fromCacheBytes(bytes(9), root, truncated));
            assertThrows(LeanPqException.class, () -> VrfKey.fromCacheBytes(bytes(9), new byte[32], cache));
            assertThrows(IllegalArgumentException.class, () -> VrfKey.fromCacheBytes(new byte[31], root, cache));
        }
    }

    @Test
    void vrfRejectsBadInput() {
        try (VrfKey key = VrfKey.fromSeed(bytes(9), 100, 200)) {
            assertThrows(LeanPqException.class, () -> key.proof(99));
            assertThrows(LeanPqException.class, () -> key.proof(200));
        }
        assertThrows(LeanPqException.class, () -> VrfKey.fromSeed(bytes(9), 100, 100));
        assertThrows(LeanPqException.class, () -> VrfKey.fromSeed(bytes(9), 0, (1L << 31) + 1));
        assertThrows(IllegalArgumentException.class, () -> VrfKey.fromSeed(new byte[31], 100, 200));
    }

    @Test
    @DisabledOnOs(OS.WINDOWS)
    void aggregatesBothSchemesRecursively() {
        Sidecar sidecar = Shared.SIDECAR;
        assertTrue(PROVERS.contains(sidecar.prover()));
        byte[] first = bytes(0x11);
        byte[] second = bytes(0x22);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(5));
             SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(bytes(6))) {
            byte[] xmssKey = xmss.publicKey();
            byte[] sphincsKey = sphincs.publicKey();
            try (Aggregate left = sidecar.aggregate(
                     List.of(), List.of(new SignedMessage(xmssKey, first, xmss.sign(first, 0))), List.of());
                 Aggregate right = sidecar.aggregate(
                     List.of(), List.of(), List.of(new SignedMessage(sphincsKey, second, sphincs.sign(second))));
                 Aggregate root = sidecar.aggregate(
                     List.of(left, right), List.of(new SignedMessage(xmssKey, second, xmss.sign(second, 1))), List.of());
                 Aggregate received = sidecar.verify(root.toBytes(), root.xmssClaims(), root.sphincsClaims())) {
                List<SignatureClaim> xmssClaims = received.xmssClaims();
                assertEquals(2, xmssClaims.size());
                assertEquals(
                    Set.of(new SignatureClaim(xmssKey, first), new SignatureClaim(xmssKey, second)),
                    Set.copyOf(xmssClaims));
                assertEquals(List.of(new SignatureClaim(sphincsKey, second)), received.sphincsClaims());
                assertArrayEquals(root.toBytes(), received.toBytes());

                byte[] proof = root.toBytes();
                List<SignatureClaim> sphincsClaims = root.sphincsClaims();
                // The receiver may list the claims in any order, and a repeated claim counts once.
                List<SignatureClaim> reordered = List.of(xmssClaims.get(1), xmssClaims.get(0), xmssClaims.get(1));
                try (Aggregate rebuilt = sidecar.verify(proof, reordered, sphincsClaims)) {
                    assertEquals(xmssClaims, rebuilt.xmssClaims());
                    assertEquals(sphincsClaims, rebuilt.sphincsClaims());
                }

                assertThrows(LeanPqException.class,
                    () -> sidecar.verify(proof, List.of(xmssClaims.get(0)), sphincsClaims));
                assertThrows(LeanPqException.class,
                    () -> sidecar.verify(proof, xmssClaims, List.of()));
                assertThrows(LeanPqException.class, () -> sidecar.verify(proof,
                    List.of(new SignatureClaim(xmssKey, first), new SignatureClaim(xmssKey, bytes(0x33))), sphincsClaims));
                assertThrows(LeanPqException.class, () -> sidecar.verify(proof, sphincsClaims, xmssClaims));

                byte[] tampered = proof.clone();
                tampered[tampered.length - 1] ^= 1;
                assertThrows(LeanPqException.class, () -> sidecar.verify(tampered, xmssClaims, sphincsClaims));
                byte[] truncated = Arrays.copyOf(proof, proof.length - 1);
                assertThrows(LeanPqException.class, () -> sidecar.verify(truncated, xmssClaims, sphincsClaims));
                assertThrows(LeanPqException.class, () -> sidecar.verify(new byte[0], xmssClaims, sphincsClaims));
            }
        }
    }

    @Test
    @DisabledOnOs(OS.WINDOWS)
    void rejectsAnEmptyAggregation() {
        assertThrows(LeanPqException.class, () -> Shared.SIDECAR.aggregate(List.of(), List.of(), List.of()));
    }

    @Test
    @DisabledOnOs(OS.WINDOWS)
    void startsAndStopsItsOwnSidecar(@TempDir Path directory) {
        Path socket = directory.resolve("s.sock");
        byte[] proof = Shared.LEAF.toBytes();
        List<SignatureClaim> claims = Shared.LEAF.xmssClaims();
        Path binary = Path.of(environment("LEANVM_SIDECAR_BIN"));
        Sidecar started = Sidecar.start(binary, socket, 2);
        try (started) {
            assertTrue(PROVERS.contains(started.prover()));
            try (Aggregate verified = started.verify(proof, claims, List.of())) {
                assertEquals(claims, verified.xmssClaims());
            }
            assertTrue(assertThrows(LeanPqException.class, () -> Sidecar.start(binary, socket))
                .getMessage().contains("already listens"));
        }
        assertThrows(IllegalStateException.class, () -> started.verify(proof, claims, List.of()));
        // Closing it stopped the sidecar.
        assertThrows(LeanPqException.class, () -> Sidecar.connect(socket));
    }

    @Test
    @EnabledOnOs(OS.WINDOWS)
    void cannotConnectWithoutUnixSockets() {
        assertThrows(LeanPqException.class, () -> Sidecar.connect(Path.of("sidecar.sock")));
    }

    /** The sidecar at {@code LEANVM_SIDECAR_SOCKET}, and one aggregate it proved, made on first use. */
    private static final class Shared {
        static final Sidecar SIDECAR = Sidecar.connect(Path.of(environment("LEANVM_SIDECAR_SOCKET")));
        static final Aggregate LEAF = leaf();

        private static Aggregate leaf() {
            byte[] message = bytes(0x44);
            try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(7))) {
                return SIDECAR.aggregate(List.of(), List.of(new SignedMessage(xmss.publicKey(), message, xmss.sign(message, 0))), List.of());
            }
        }
    }

    private static String environment(String name) {
        String value = System.getenv(name);
        if (value == null || value.isEmpty()) {
            throw new IllegalStateException("set " + name + " to run the aggregation tests");
        }
        return value;
    }

    private static byte[] bytes(int value) {
        byte[] bytes = new byte[32];
        Arrays.fill(bytes, (byte) value);
        return bytes;
    }
}
