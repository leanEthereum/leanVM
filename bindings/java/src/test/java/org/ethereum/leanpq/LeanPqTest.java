package org.ethereum.leanpq;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
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
            try (XmssSecretKey loaded = XmssSecretKey.fromCacheBytes(bytes(7), cache)) {
                assertArrayEquals(xmss.publicKey(), loaded.publicKey());
                assertArrayEquals(cache, loaded.cacheToBytes());
                byte[] signature = loaded.sign(message, 3);
                assertArrayEquals(xmss.sign(message, 3), signature);
                assertTrue(LeanPq.xmssVerify(xmss.publicKey(), message, signature));
            }
            byte[] truncated = Arrays.copyOf(cache, cache.length - 1);
            assertThrows(LeanPqException.class, () -> XmssSecretKey.fromCacheBytes(bytes(7), truncated));
            assertThrows(IllegalArgumentException.class, () -> XmssSecretKey.fromCacheBytes(new byte[31], cache));
        }
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

    private static byte[] bytes(int value) {
        byte[] bytes = new byte[32];
        Arrays.fill(bytes, (byte) value);
        return bytes;
    }
}
