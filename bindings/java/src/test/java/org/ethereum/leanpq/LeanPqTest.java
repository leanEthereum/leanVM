package org.ethereum.leanpq;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.HexFormat;
import java.util.List;
import java.util.Set;
import org.junit.jupiter.api.Test;

class LeanPqTest {
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
    void aggregatesBothSchemesRecursively() {
        byte[] first = bytes(0x11);
        byte[] second = bytes(0x22);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(bytes(5));
             SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(bytes(6))) {
            byte[] xmssKey = xmss.publicKey();
            byte[] sphincsKey = sphincs.publicKey();
            try (Aggregate left = LeanPq.aggregate(
                     List.of(), List.of(new SignedMessage(xmssKey, first, xmss.sign(first, 0))), List.of());
                 Aggregate right = LeanPq.aggregate(
                     List.of(), List.of(), List.of(new SignedMessage(sphincsKey, second, sphincs.sign(second))));
                 Aggregate root = LeanPq.aggregate(
                     List.of(left, right), List.of(new SignedMessage(xmssKey, second, xmss.sign(second, 1))), List.of());
                 Aggregate received = Aggregate.fromBytes(root.toBytes(), root.xmssClaims(), root.sphincsClaims())) {
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
                try (Aggregate rebuilt = Aggregate.fromBytes(proof, reordered, sphincsClaims)) {
                    assertEquals(xmssClaims, rebuilt.xmssClaims());
                    assertEquals(sphincsClaims, rebuilt.sphincsClaims());
                }

                assertThrows(LeanPqException.class,
                    () -> Aggregate.fromBytes(proof, List.of(xmssClaims.get(0)), sphincsClaims));
                assertThrows(LeanPqException.class,
                    () -> Aggregate.fromBytes(proof, xmssClaims, List.of()));
                assertThrows(LeanPqException.class, () -> Aggregate.fromBytes(proof,
                    List.of(new SignatureClaim(xmssKey, first), new SignatureClaim(xmssKey, bytes(0x33))), sphincsClaims));
                assertThrows(LeanPqException.class, () -> Aggregate.fromBytes(proof, sphincsClaims, xmssClaims));

                // Re-aggregating the root can keep only some of its claims, each one it covers.
                try (Aggregate only = LeanPq.aggregateOnly(
                         List.of(root), List.of(), List.of(), List.of(xmssClaims.get(0)), List.of())) {
                    assertEquals(List.of(xmssClaims.get(0)), only.xmssClaims());
                    assertEquals(List.of(), only.sphincsClaims());
                }
                LeanPqException uncovered = assertThrows(LeanPqException.class, () -> LeanPq.aggregateOnly(
                    List.of(root), List.of(), List.of(), List.of(new SignatureClaim(xmssKey, bytes(0x33))), List.of()));
                assertTrue(uncovered.getMessage().contains("not covered by the inputs"), uncovered.getMessage());

                byte[] tampered = proof.clone();
                tampered[tampered.length - 1] ^= 1;
                assertThrows(LeanPqException.class, () -> Aggregate.fromBytes(tampered, xmssClaims, sphincsClaims));
                byte[] truncated = Arrays.copyOf(proof, proof.length - 1);
                assertThrows(LeanPqException.class, () -> Aggregate.fromBytes(truncated, xmssClaims, sphincsClaims));
                assertThrows(LeanPqException.class, () -> Aggregate.fromBytes(new byte[0], xmssClaims, sphincsClaims));
            }
        }
    }

    @Test
    void rejectsAnEmptyAggregation() {
        assertThrows(LeanPqException.class, () -> LeanPq.aggregate(List.of(), List.of(), List.of()));
    }

    @Test
    void setupKeepsItsFirstThreadCount() {
        // 0, the count aggregating starts the prover with.
        LeanPq.setup(0);
        assertThrows(LeanPqException.class, () -> LeanPq.setup(1));
    }

    private static byte[] bytes(int value) {
        byte[] bytes = new byte[32];
        Arrays.fill(bytes, (byte) value);
        return bytes;
    }
}
