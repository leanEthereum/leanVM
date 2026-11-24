{.used.}

import
  std/[algorithm, os, strutils],
  unittest2,
  ../lean_pq

func filled(value: byte): array[32, byte] =
  for index in 0 ..< result.len:
    result[index] = value

func claimKey(claim: LeanPqClaim): string =
  for value in claim.publicKey:
    result.add char(value)
  for value in claim.message:
    result.add char(value)

func sortedClaims(claims: openArray[LeanPqClaim]): seq[LeanPqClaim] =
  claims.sorted(proc(a, b: LeanPqClaim): int = cmp(claimKey(a), claimKey(b)))

func fromHex(text: string): seq[byte] =
  for index in countup(0, text.len - 1, 2):
    result.add byte(fromHex[uint8](text[index .. index + 1]))

const
  message = filled(0x42)
  otherMessage = filled(0x43)
  knownAnswer = currentSourcePath().parentDir() / ".." / ".." / ".." / "crates" / "lean_sphincs" / "tests" /
    "lean_sphincs" / "known_answer.hex"

suite "lean_pq":
  test "native record layouts":
    check:
      sizeof(XmssSignedMessage) == 2468
      sizeof(SphincsSignedMessage) == 7804
      sizeof(LeanPqClaim) == 64

  test "leanXMSS signs and verifies":
    let
      key = XmssSecretKey.fromSeed(filled(1)).expect("key")
      publicKey = key.publicKey().expect("public key")
    check key.prepare(7).isOk()
    let signature = key.sign(message, 7).expect("signature")

    check:
      xmssVerify(publicKey, message, signature)
      not xmssVerify(publicKey, otherMessage, signature)

  test "leanXMSS key loads from its tree cache":
    let
      seed = filled(6)
      key = XmssSecretKey.fromSeed(seed).expect("key")
    check key.prepare(3).isOk()
    let
      cache = key.cacheToBytes().expect("cache")
      publicKey = key.publicKey().expect("public key")
      loaded = XmssSecretKey.fromCacheBytes(seed, publicKey, cache).expect("loaded key")
      signature = loaded.sign(message, 3).expect("signature")
      otherKey = XmssSecretKey.fromSeed(filled(7)).expect("key").publicKey().expect("public key")
    var tampered = cache
    tampered[0] = tampered[0] xor 1

    check:
      loaded.publicKey().expect("public key") == publicKey
      signature == key.sign(message, 3).expect("signature")
      xmssVerify(publicKey, message, signature)
      XmssSecretKey.fromCacheBytes(seed, publicKey, cache.toOpenArray(1, cache.high)).isErr()
      XmssSecretKey.fromCacheBytes(seed, publicKey, tampered).isErr()
      XmssSecretKey.fromCacheBytes(seed, otherKey, cache).isErr()

  test "leanSPHINCS signs and verifies":
    let
      seed = filled(2)
      key = SphincsSecretKey.fromSeed(seed).expect("key")
      publicKey = key.publicKey().expect("public key")
      signature = key.sign(message).expect("signature")

    check:
      key.toBytes().expect("bytes") == seed
      sphincsVerify(publicKey, message, signature)
      not sphincsVerify(publicKey, otherMessage, signature)

  test "leanSPHINCS reproduces the known answer":
    var seed, knownMessage: array[32, byte]
    for index in 0 ..< 32:
      seed[index] = byte((37 * index + 11) mod 256)
      knownMessage[index] = byte((7 * index + 3) mod 256)
    let lines = readFile(knownAnswer).splitWhitespace()
    var
      publicKey: SphincsPublicKey
      signature: SphincsSignature
    let
      publicKeyBytes = fromHex(lines[0])
      signatureBytes = fromHex(lines[1])
    require:
      publicKeyBytes.len == publicKey.len
      signatureBytes.len == signature.len
    copyMem(addr publicKey[0], addr publicKeyBytes[0], publicKey.len)
    copyMem(addr signature[0], addr signatureBytes[0], signature.len)

    let key = SphincsSecretKey.fromSeed(seed).expect("key")
    check:
      key.publicKey().expect("public key") == publicKey
      key.sign(knownMessage).expect("signature") == signature
      sphincsVerify(publicKey, knownMessage, signature)

  test "VRF key opens its slots":
    let
      seed = filled(9)
      key = VrfKey.init(seed, 100, 200).expect("key")
      vrfRoot = key.root().expect("root")
      vrfProof = key.proof(150).expect("proof")
    check:
      @vrfRoot == fromHex("c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45")
      vrfVerify(vrfRoot, 150, vrfProof)
      not vrfVerify(vrfRoot, 151, vrfProof)
      vrfVerify(vrfRoot, 100, key.proof(100).expect("proof"))
      vrfVerify(vrfRoot, 199, key.proof(199).expect("proof"))
      key.proof(99).isErr()
      key.proof(200).isErr()
      VrfKey.init(seed, 5, 5).isErr()
      VrfKey.init(seed, 0, (1'u32 shl 31) + 1).isErr()

  test "VRF key loads from its cache":
    let
      seed = filled(9)
      key = VrfKey.init(seed, 100, 200).expect("key")
      cache = key.cacheToBytes().expect("cache")
      vrfRoot = key.root().expect("root")
      loaded = VrfKey.fromCacheBytes(seed, vrfRoot, cache).expect("loaded key")
    check:
      @vrfRoot == fromHex("c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45")
      loaded.cacheToBytes().expect("cache") == cache
      vrfVerify(vrfRoot, 150, loaded.proof(150).expect("proof"))
      VrfKey.fromCacheBytes(seed, vrfRoot, cache.toOpenArray(0, cache.len - 2)).isErr()
      VrfKey.fromCacheBytes(seed, default(VrfRoot), cache).isErr()

  test "secret keys round trip through bytes":
    let
      xmss = XmssSecretKey.generate().expect("key")
      xmssRestored = XmssSecretKey.fromBytes(xmss.toBytes().expect("bytes")).expect("restored")
    check xmssRestored.publicKey().expect("restored") == xmss.publicKey().expect("original")

    let
      sphincs = SphincsSecretKey.generate().expect("key")
      sphincsBytes = sphincs.toBytes().expect("bytes")
      sphincsRestored = SphincsSecretKey.fromBytes(sphincsBytes).expect("restored")
    check:
      sphincsRestored.publicKey().expect("restored") == sphincs.publicKey().expect("original")
      sphincsRestored.toBytes().expect("restored bytes") == sphincsBytes

  test "malformed input returns an error":
    check:
      XmssSecretKey.fromBytes([1'u8, 2, 3]).isErr()
      SphincsSecretKey.fromBytes([]).isErr()

  test "closed values return errors and close twice":
    let
      xmss = XmssSecretKey.fromSeed(filled(8)).expect("key")
      sphincs = SphincsSecretKey.fromSeed(filled(9)).expect("key")
      vrf = VrfKey.init(filled(10), 0, 1).expect("key")
    xmss.close()
    xmss.close()
    sphincs.close()
    vrf.close()
    vrf.close()
    check:
      xmss.publicKey().error() == "leanXMSS secret key is closed"
      xmss.sign(message, 0).isErr()
      sphincs.sign(message).isErr()
      vrf.root().error() == "VRF key is closed"
      vrf.proof(0).isErr()
    let nilKey: XmssSecretKey = nil
    nilKey.close()
    check nilKey.toBytes().isErr()

  test "aggregates recursively and round trips through bytes":
    let
      xmssKey = XmssSecretKey.fromSeed(filled(3)).expect("key")
      sphincsKey = SphincsSecretKey.fromSeed(filled(4)).expect("key")
      extraKey = XmssSecretKey.fromSeed(filled(5)).expect("key")
      xmssPublicKey = xmssKey.publicKey().expect("public key")
      sphincsPublicKey = sphincsKey.publicKey().expect("public key")
      extraPublicKey = extraKey.publicKey().expect("public key")

    let
      xmssLeaf = LeanPqAggregate.init(xmss = [XmssSignedMessage(
        publicKey: xmssPublicKey, message: message,
        signature: xmssKey.sign(message, 0).expect("signature"))]).expect("xmss leaf")
      sphincsLeaf = LeanPqAggregate.init(sphincs = [SphincsSignedMessage(
        publicKey: sphincsPublicKey, message: message,
        signature: sphincsKey.sign(message).expect("signature"))]).expect("sphincs leaf")
      root = LeanPqAggregate.init([xmssLeaf, sphincsLeaf], [XmssSignedMessage(
        publicKey: extraPublicKey, message: otherMessage,
        signature: extraKey.sign(otherMessage, 0).expect("signature"))]).expect("root")

    let
      expectedXmss = [
        LeanPqClaim(publicKey: xmssPublicKey, message: message),
        LeanPqClaim(publicKey: extraPublicKey, message: otherMessage)]
      expectedSphincs = [LeanPqClaim(publicKey: sphincsPublicKey, message: message)]
      encoded = root.toBytes().expect("bytes")
      restored = LeanPqAggregate.fromBytes(
        encoded, root.xmssClaims().expect("claims"), root.sphincsClaims().expect("claims")
      ).expect("restored")
    check:
      restored.xmssClaims().expect("claims") == sortedClaims(expectedXmss)
      restored.sphincsClaims().expect("claims") == @expectedSphincs
      restored.toBytes().expect("bytes") == encoded

    # Claims in any order, a repeated claim counting once.
    let reordered = LeanPqAggregate.fromBytes(
      encoded, [expectedXmss[1], expectedXmss[0], expectedXmss[1]], expectedSphincs
    ).expect("reordered")
    check reordered.xmssClaims().expect("claims") == sortedClaims(expectedXmss)

    # The proof attests exactly its claims: one short, one extra or another message fails.
    check:
      LeanPqAggregate.fromBytes(encoded, [expectedXmss[0]], expectedSphincs).isErr()
      LeanPqAggregate.fromBytes(encoded, expectedXmss).isErr()
      LeanPqAggregate.fromBytes(encoded, expectedXmss, [
        expectedSphincs[0],
        LeanPqClaim(publicKey: sphincsPublicKey, message: otherMessage)]).isErr()
      LeanPqAggregate.fromBytes(encoded, expectedXmss, [
        LeanPqClaim(publicKey: sphincsPublicKey, message: otherMessage)]).isErr()
      LeanPqAggregate.fromBytes(encoded, expectedSphincs, expectedXmss).isErr()

    # Re-aggregating the root can keep only some of its claims, each one it covers.
    let only = LeanPqAggregate.initOnly([root], xmssClaims = [expectedXmss[0]]).expect("only")
    check:
      only.xmssClaims().expect("claims") == @[expectedXmss[0]]
      only.sphincsClaims().expect("claims").len == 0
      LeanPqAggregate.initOnly([root], xmssClaims = [
        LeanPqClaim(publicKey: xmssPublicKey, message: otherMessage)]).error().contains("not covered by the inputs")

    var tampered = encoded
    tampered[tampered.len div 2] = tampered[tampered.len div 2] xor 1
    check:
      LeanPqAggregate.fromBytes(tampered, expectedXmss, expectedSphincs).isErr()
      LeanPqAggregate.fromBytes(
        encoded.toOpenArray(0, encoded.len - 2), expectedXmss, expectedSphincs).isErr()
      LeanPqAggregate.fromBytes([0'u8]).isErr()
      LeanPqAggregate.init().isErr()

    restored.close()
    check:
      restored.toBytes().isErr()
      LeanPqAggregate.init([root, restored]).error() == "aggregate is closed"

  test "setup keeps its thread count":
    check:
      leanPqSetup(0).isOk()
      leanPqSetup(0).isOk()
      leanPqSetup(1).isErr()
