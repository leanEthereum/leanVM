using NUnit.Framework;

namespace Ethereum.PostQuantum.Tests;

public class LeanPqTests
{
    private static readonly byte[] VrfRoot = Convert.FromHexString("c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45");

    [Test]
    public void SignsVerifiesAndRejectsAnotherMessage()
    {
        byte[] message = Bytes(0x42);
        byte[] other = Bytes(0x43);
        using XmssSecretKey xmss = XmssSecretKey.FromSeed(Bytes(1));
        using SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(Bytes(2));

        byte[] xmssSignature = xmss.Sign(message, 3);
        Assert.That(xmssSignature, Has.Length.EqualTo(LeanPq.XmssSignatureLength));
        Assert.That(LeanPq.XmssVerify(xmss.GetPublicKey(), message, xmssSignature), Is.True);
        Assert.That(LeanPq.XmssVerify(xmss.GetPublicKey(), other, xmssSignature), Is.False);

        byte[] sphincsSignature = sphincs.Sign(message);
        Assert.That(sphincsSignature, Has.Length.EqualTo(LeanPq.SphincsSignatureLength));
        Assert.That(LeanPq.SphincsVerify(sphincs.GetPublicKey(), message, sphincsSignature), Is.True);
        Assert.That(LeanPq.SphincsVerify(sphincs.GetPublicKey(), other, sphincsSignature), Is.False);
    }

    [Test]
    public void SecretKeysRoundTripThroughBytes()
    {
        byte[] message = Bytes(7);
        using (XmssSecretKey xmss = XmssSecretKey.FromSeed(Bytes(3)))
        using (XmssSecretKey restored = XmssSecretKey.FromBytes(xmss.ToBytes()))
        {
            Assert.That(restored.GetPublicKey(), Is.EqualTo(xmss.GetPublicKey()));
            Assert.That(LeanPq.XmssVerify(xmss.GetPublicKey(), message, restored.Sign(message, 9)), Is.True);
        }
        using (SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(Bytes(4)))
        using (SphincsSecretKey restored = SphincsSecretKey.FromBytes(sphincs.ToBytes()))
        {
            Assert.That(sphincs.ToBytes(), Is.EqualTo(Bytes(4)));
            Assert.That(restored.GetPublicKey(), Is.EqualTo(sphincs.GetPublicKey()));
            Assert.That(LeanPq.SphincsVerify(sphincs.GetPublicKey(), message, restored.Sign(message)), Is.True);
        }
    }

    [Test]
    public void XmssKeyLoadsFromItsTreeCache()
    {
        byte[] message = Bytes(7);
        using XmssSecretKey xmss = XmssSecretKey.FromSeed(Bytes(7));
        xmss.Prepare(3);
        byte[] cache = xmss.CacheToBytes();
        byte[] publicKey = xmss.GetPublicKey();
        using (XmssSecretKey loaded = XmssSecretKey.FromCacheBytes(Bytes(7), publicKey, cache))
        {
            Assert.That(loaded.GetPublicKey(), Is.EqualTo(publicKey));
            Assert.That(loaded.CacheToBytes(), Is.EqualTo(cache));
            byte[] signature = loaded.Sign(message, 3);
            Assert.That(signature, Is.EqualTo(xmss.Sign(message, 3)));
            Assert.That(LeanPq.XmssVerify(publicKey, message, signature), Is.True);
        }

        byte[] tampered = (byte[])cache.Clone();
        tampered[0] ^= 1;
        byte[] otherKey;
        using (XmssSecretKey other = XmssSecretKey.FromSeed(Bytes(8)))
        {
            otherKey = other.GetPublicKey();
        }
        Assert.Throws<LeanPqException>(() => XmssSecretKey.FromCacheBytes(Bytes(7), publicKey, cache.AsSpan(..^1)));
        Assert.Throws<LeanPqException>(() => XmssSecretKey.FromCacheBytes(Bytes(7), publicKey, tampered));
        Assert.Throws<LeanPqException>(() => XmssSecretKey.FromCacheBytes(Bytes(7), otherKey, cache));
        Assert.Throws<ArgumentException>(() => XmssSecretKey.FromCacheBytes(new byte[31], publicKey, cache));
    }

    [Test]
    public void VrfMatchesThePinnedVector()
    {
        using VrfKey key = VrfKey.FromSeed(Bytes(9), 100, 200);
        Assert.That(key.GetRoot(), Is.EqualTo(VrfRoot));
        byte[] proof = key.GetProof(150);
        Assert.That(proof, Has.Length.EqualTo(LeanPq.VrfProofLength));
        Assert.That(LeanPq.VrfVerify(VrfRoot, 150, proof), Is.True);
        Assert.That(LeanPq.VrfVerify(VrfRoot, 151, proof), Is.False);
        Assert.That(LeanPq.VrfVerify(VrfRoot, 150, proof.AsSpan(..^1)), Is.False);
        foreach (uint slot in new uint[] { 100, 199 })
        {
            Assert.That(LeanPq.VrfVerify(VrfRoot, slot, key.GetProof(slot)), Is.True);
        }
    }

    [Test]
    public void VrfKeyLoadsFromItsCache()
    {
        using VrfKey key = VrfKey.FromSeed(Bytes(9), 100, 200);
        byte[] cache = key.CacheToBytes();
        using (VrfKey loaded = VrfKey.FromCacheBytes(Bytes(9), VrfRoot, cache))
        {
            Assert.That(loaded.CacheToBytes(), Is.EqualTo(cache));
            Assert.That(LeanPq.VrfVerify(VrfRoot, 150, loaded.GetProof(150)), Is.True);
        }
        Assert.Throws<LeanPqException>(() => VrfKey.FromCacheBytes(Bytes(9), VrfRoot, cache.AsSpan(..^1)));
        Assert.Throws<LeanPqException>(() => VrfKey.FromCacheBytes(Bytes(9), new byte[32], cache));
        Assert.Throws<ArgumentException>(() => VrfKey.FromCacheBytes(new byte[31], VrfRoot, cache));
    }

    [Test]
    public void VrfRejectsBadInput()
    {
        using (VrfKey key = VrfKey.FromSeed(Bytes(9), 100, 200))
        {
            Assert.Throws<LeanPqException>(() => key.GetProof(99));
            Assert.Throws<LeanPqException>(() => key.GetProof(200));
        }
        Assert.Throws<LeanPqException>(() => VrfKey.FromSeed(Bytes(9), 100, 100));
        Assert.Throws<LeanPqException>(() => VrfKey.FromSeed(Bytes(9), 0, (1u << 31) + 1));
        Assert.Throws<ArgumentException>(() => VrfKey.FromSeed(new byte[31], 100, 200));
    }

    [Test]
    public void DisposedKeysRefuseCalls()
    {
        XmssSecretKey xmss = XmssSecretKey.FromSeed(Bytes(1));
        xmss.Dispose();
        xmss.Dispose();
        Assert.Throws<ObjectDisposedException>(() => xmss.GetPublicKey());
        Assert.Throws<ObjectDisposedException>(() => xmss.Sign(Bytes(2), 0));
    }

    [Test]
    public void NativeErrorsStayOnTheirThread()
    {
        string rangeError = Assert.Throws<LeanPqException>(() => VrfKey.FromSeed(Bytes(9), 100, 100).Dispose())!.Message;
        int workers = 4 * Environment.ProcessorCount;
        string?[] failures = new string?[workers];

        Parallel.For(0, workers, new ParallelOptions { MaxDegreeOfParallelism = workers }, worker =>
        {
            for (int iteration = 0; iteration < 1000 && failures[worker] is null; iteration++)
            {
                failures[worker] = ErrorMessage(() => XmssSecretKey.FromBytes([1]).Dispose()) switch
                {
                    "leanXMSS secret key must be 32 bytes, got 1" => ErrorMessage(() => VrfKey.FromSeed(Bytes(9), 100, 100).Dispose()) == rangeError ? null : "range",
                    string other => other,
                    null => "no error",
                };
            }
        });

        Assert.That(failures, Is.All.Null);
    }

    [Test]
    public void AggregatesBothSchemesRecursively()
    {
        byte[] first = Bytes(0x11);
        byte[] second = Bytes(0x22);
        using XmssSecretKey xmss = XmssSecretKey.FromSeed(Bytes(5));
        using SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(Bytes(6));
        byte[] xmssKey = xmss.GetPublicKey();
        byte[] sphincsKey = sphincs.GetPublicKey();

        using Aggregate left = LeanPq.Aggregate([], [new SignedMessage(xmssKey, first, xmss.Sign(first, 0))], []);
        using Aggregate right = LeanPq.Aggregate([], [], [new SignedMessage(sphincsKey, second, sphincs.Sign(second))]);
        using Aggregate root = LeanPq.Aggregate([left, right], [new SignedMessage(xmssKey, second, xmss.Sign(second, 1))], []);
        using Aggregate received = Aggregate.FromBytes(root.ToBytes(), root.GetXmssClaims(), root.GetSphincsClaims());

        IReadOnlyList<SignatureClaim> xmssClaims = received.GetXmssClaims();
        Assert.That(xmssClaims, Is.EquivalentTo(new[] { new SignatureClaim(xmssKey, first), new SignatureClaim(xmssKey, second) }));
        IReadOnlyList<SignatureClaim> sphincsClaims = root.GetSphincsClaims();
        Assert.That(received.GetSphincsClaims(), Is.EqualTo(new[] { new SignatureClaim(sphincsKey, second) }));
        byte[] proof = root.ToBytes();
        Assert.That(received.ToBytes(), Is.EqualTo(proof));

        // The receiver may list the claims in any order, and a repeated claim counts once.
        using (Aggregate rebuilt = Aggregate.FromBytes(proof, [xmssClaims[1], xmssClaims[0], xmssClaims[1]], sphincsClaims))
        {
            Assert.That(rebuilt.GetXmssClaims(), Is.EqualTo(xmssClaims));
            Assert.That(rebuilt.GetSphincsClaims(), Is.EqualTo(sphincsClaims));
        }

        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(proof, [xmssClaims[0]], sphincsClaims));
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(proof, xmssClaims, []));
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(proof, [new SignatureClaim(xmssKey, first), new SignatureClaim(xmssKey, Bytes(0x33))], sphincsClaims));
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(proof, sphincsClaims, xmssClaims));

        // Re-aggregating the root can keep only some of its claims, each one it covers.
        using (Aggregate only = LeanPq.AggregateOnly([root], [], [], [xmssClaims[0]], []))
        {
            Assert.That(only.GetXmssClaims(), Is.EqualTo(new[] { xmssClaims[0] }));
            Assert.That(only.GetSphincsClaims(), Is.Empty);
        }
        LeanPqException uncovered = Assert.Throws<LeanPqException>(() => LeanPq.AggregateOnly([root], [], [], [new SignatureClaim(xmssKey, Bytes(0x33))], []))!;
        Assert.That(uncovered.Message, Does.Contain("not covered by the inputs"));

        byte[] tampered = (byte[])proof.Clone();
        tampered[^1] ^= 1;
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(tampered, xmssClaims, sphincsClaims));
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes(proof.AsSpan(..^1), xmssClaims, sphincsClaims));
        Assert.Throws<LeanPqException>(() => Aggregate.FromBytes([], xmssClaims, sphincsClaims));
    }

    [Test]
    public void RejectsAnEmptyAggregation() =>
        Assert.Throws<LeanPqException>(() => LeanPq.Aggregate([], [], []));

    [Test]
    public void SetupKeepsItsFirstThreadCount()
    {
        // 0 also passes after an earlier test's aggregation started the prover, with 0 threads.
        LeanPq.Setup(0);
        Assert.Throws<LeanPqException>(() => LeanPq.Setup(1));
        Assert.Throws<ArgumentOutOfRangeException>(() => LeanPq.Setup(-1));
    }

    private static string? ErrorMessage(Action action)
    {
        try
        {
            action();
            return null;
        }
        catch (LeanPqException error)
        {
            return error.Message;
        }
    }

    private static byte[] Bytes(byte value)
    {
        byte[] bytes = new byte[32];
        Array.Fill(bytes, value);
        return bytes;
    }
}
