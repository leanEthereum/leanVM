import os
import sys

import py_lean_pq as lpq
import pytest

MESSAGE = b"\x42" * 32
OTHER_MESSAGE = b"\x43" * 32


def test_xmss_signs_and_verifies():
    key = lpq.XmssSecretKey.from_seed(b"\x01" * 32)
    key.prepare(3)
    signature = key.sign(MESSAGE, 3)

    assert lpq.xmss_verify(key.public_key, MESSAGE, signature) is None
    with pytest.raises(lpq.LeanPqError):
        lpq.xmss_verify(key.public_key, OTHER_MESSAGE, signature)


def test_sphincs_signs_and_verifies():
    key = lpq.SphincsSecretKey.from_seed(b"\x02" * 32)
    signature = key.sign(MESSAGE)
    assert len(signature) == 7740

    assert lpq.sphincs_verify(key.public_key, MESSAGE, signature) is None
    with pytest.raises(lpq.LeanPqError):
        lpq.sphincs_verify(key.public_key, OTHER_MESSAGE, signature)


def test_secret_keys_round_trip_through_bytes():
    xmss_key = lpq.XmssSecretKey.from_seed(b"\x03" * 32)
    restored_xmss = lpq.XmssSecretKey.from_bytes(xmss_key.to_bytes())
    assert restored_xmss.public_key == xmss_key.public_key
    lpq.xmss_verify(xmss_key.public_key, MESSAGE, restored_xmss.sign(MESSAGE, 9))

    sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x04" * 32)
    assert len(sphincs_key.to_bytes()) == 32
    restored_sphincs = lpq.SphincsSecretKey.from_bytes(sphincs_key.to_bytes())
    assert restored_sphincs.public_key == sphincs_key.public_key
    lpq.sphincs_verify(sphincs_key.public_key, MESSAGE, restored_sphincs.sign(MESSAGE))

    with pytest.raises(ValueError, match="secret key must be 32 bytes"):
        lpq.XmssSecretKey.from_bytes(b"\x03" * 31)
    with pytest.raises(ValueError, match="secret key must be 32 bytes"):
        lpq.SphincsSecretKey.from_bytes(b"\x04" * 33)


def test_xmss_key_loads_from_its_tree_cache():
    seed = b"\x07" * 32
    key = lpq.XmssSecretKey.from_seed(seed)
    key.prepare(3)
    cache = key.cache_to_bytes()

    loaded = lpq.XmssSecretKey.from_cache_bytes(seed, key.public_key, cache)
    assert loaded.public_key == key.public_key
    assert loaded.cache_to_bytes() == cache
    signature = loaded.sign(MESSAGE, 3)
    assert signature == key.sign(MESSAGE, 3)
    lpq.xmss_verify(key.public_key, MESSAGE, signature)

    # A truncated cache, a tampered one, or another key's is refused.
    tampered = bytes([cache[0] ^ 1]) + cache[1:]
    other = lpq.XmssSecretKey.from_seed(b"\x08" * 32).public_key
    for public_key, data in [(key.public_key, cache[1:]), (key.public_key, tampered), (other, cache)]:
        with pytest.raises(ValueError, match="not this leanXMSS key's tree cache"):
            lpq.XmssSecretKey.from_cache_bytes(seed, public_key, data)
    with pytest.raises(ValueError, match="seed must be exactly 32 bytes"):
        lpq.XmssSecretKey.from_cache_bytes(seed[1:], key.public_key, cache)


def test_aggregates_both_schemes_recursively():
    first = b"\x11" * 32
    second = b"\x22" * 32
    xmss_key = lpq.XmssSecretKey.from_seed(b"\x05" * 32)
    sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x06" * 32)

    left = lpq.aggregate(
        xmss=[(xmss_key.public_key, first, xmss_key.sign(first, 0))]
    )
    right = lpq.aggregate(
        sphincs=[(sphincs_key.public_key, second, sphincs_key.sign(second))]
    )
    root = lpq.aggregate(
        children=[left, right],
        xmss=[(xmss_key.public_key, second, xmss_key.sign(second, 1))],
    )

    xmss_claims = sorted([(xmss_key.public_key, first), (xmss_key.public_key, second)])
    sphincs_claims = [(sphincs_key.public_key, second)]
    assert root.xmss_claims == xmss_claims
    assert root.sphincs_claims == sphincs_claims

    proof = root.to_bytes()
    received = lpq.Aggregate.from_bytes(proof, root.xmss_claims, root.sphincs_claims)
    assert received.xmss_claims == xmss_claims
    assert received.sphincs_claims == sphincs_claims
    assert received.to_bytes() == proof

    # Claims may arrive in any order, and a duplicate counts once.
    shuffled = lpq.Aggregate.from_bytes(
        proof,
        xmss_claims=list(reversed(xmss_claims)) + [xmss_claims[0]],
        sphincs_claims=sphincs_claims,
    )
    assert shuffled.xmss_claims == xmss_claims

    # The proof attests exactly its claims: one short, another message, or other bytes fail.
    rejected = "does not prove the given claims"
    with pytest.raises(lpq.LeanPqError, match=rejected):
        lpq.Aggregate.from_bytes(proof, xmss_claims[:1], sphincs_claims)
    with pytest.raises(lpq.LeanPqError, match=rejected):
        lpq.Aggregate.from_bytes(proof, xmss_claims, [(sphincs_key.public_key, first)])
    with pytest.raises(lpq.LeanPqError, match=rejected):
        lpq.Aggregate.from_bytes(proof)
    tampered = bytearray(proof)
    tampered[len(tampered) // 2] ^= 1
    for data in (bytes(tampered), proof[:-1], b""):
        with pytest.raises(lpq.LeanPqError, match="malformed aggregate|does not prove"):
            lpq.Aggregate.from_bytes(data, xmss_claims, sphincs_claims)

    # Re-aggregating the root can keep only some of its claims, each one it covers.
    only = lpq.aggregate(children=[root], xmss_claims=[xmss_claims[0]])
    assert only.xmss_claims == [xmss_claims[0]]
    assert only.sphincs_claims == []
    with pytest.raises(lpq.LeanPqError, match="not covered by the inputs"):
        lpq.aggregate(children=[root], xmss_claims=[(xmss_key.public_key, b"\x33" * 32)])

    with pytest.raises(ValueError, match="message must be exactly 32 bytes"):
        lpq.Aggregate.from_bytes(proof, [(xmss_key.public_key, b"\x11")])


def test_aggregating_nothing_fails():
    with pytest.raises(lpq.LeanPqError, match="aggregation failed"):
        lpq.aggregate()


def test_setup_keeps_its_first_thread_count():
    lpq.setup()
    with pytest.raises(lpq.LeanPqError, match="already started with 0 threads, not 1"):
        lpq.setup(1)


@pytest.mark.skipif(sys.platform == "win32", reason="no fork on Windows")
@pytest.mark.filterwarnings("ignore:This process .* is multi-threaded")
def test_aggregating_in_a_child_forked_after_setup_fails():
    lpq.setup()
    pid = os.fork()
    if pid == 0:
        # Whatever happens, the child must not return into pytest.
        code = 1
        try:
            lpq.aggregate()
        except lpq.LeanPqError as error:
            code = 0 if "forked" in str(error) else 3
        finally:
            os._exit(code)
    _, status = os.waitpid(pid, 0)
    assert os.waitstatus_to_exitcode(status) == 0
