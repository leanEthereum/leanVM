import os
import shutil
import sys
import tempfile

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


UNIX = sys.platform != "win32"
needs_sidecar = pytest.mark.skipif(not UNIX, reason="the sidecar needs Unix sockets")


def env(name):
    value = os.environ.get(name)
    if not value:
        pytest.fail(f"set {name} to run the aggregation tests")
    return value


@pytest.fixture(scope="module")
def sidecar():
    with lpq.Sidecar.connect(env("LEANVM_SIDECAR_SOCKET")) as sidecar:
        yield sidecar


@needs_sidecar
def test_aggregates_both_schemes_recursively(sidecar):
    first = b"\x11" * 32
    second = b"\x22" * 32
    xmss_key = lpq.XmssSecretKey.from_seed(b"\x05" * 32)
    sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x06" * 32)

    left = sidecar.aggregate(
        xmss=[(xmss_key.public_key, first, xmss_key.sign(first, 0))]
    )
    right = sidecar.aggregate(
        sphincs=[(sphincs_key.public_key, second, sphincs_key.sign(second))]
    )
    root = sidecar.aggregate(
        children=[left, right],
        xmss=[(xmss_key.public_key, second, xmss_key.sign(second, 1))],
    )

    xmss_claims = sorted([(xmss_key.public_key, first), (xmss_key.public_key, second)])
    sphincs_claims = [(sphincs_key.public_key, second)]
    assert root.xmss_claims == xmss_claims
    assert root.sphincs_claims == sphincs_claims

    proof = root.to_bytes()
    received = sidecar.verify(proof, root.xmss_claims, root.sphincs_claims)
    assert received.xmss_claims == xmss_claims
    assert received.sphincs_claims == sphincs_claims
    assert received.to_bytes() == proof

    # Claims may arrive in any order, and a duplicate counts once.
    shuffled = sidecar.verify(
        proof,
        xmss_claims=list(reversed(xmss_claims)) + [xmss_claims[0]],
        sphincs_claims=sphincs_claims,
    )
    assert shuffled.xmss_claims == xmss_claims

    # The proof attests exactly its claims: one short, another message, or other bytes fail.
    rejected = "does not prove the given claims"
    with pytest.raises(lpq.LeanPqError, match=rejected):
        sidecar.verify(proof, xmss_claims[:1], sphincs_claims)
    with pytest.raises(lpq.LeanPqError, match=rejected):
        sidecar.verify(proof, xmss_claims, [(sphincs_key.public_key, first)])
    with pytest.raises(lpq.LeanPqError, match=rejected):
        sidecar.verify(proof)
    tampered = bytearray(proof)
    tampered[len(tampered) // 2] ^= 1
    for data in (bytes(tampered), proof[:-1], b""):
        with pytest.raises(lpq.LeanPqError, match=rejected):
            sidecar.verify(data, xmss_claims, sphincs_claims)

    with pytest.raises(ValueError, match="message must be exactly 32 bytes"):
        sidecar.verify(proof, [(xmss_key.public_key, b"\x11")])


@needs_sidecar
def test_aggregating_nothing_fails(sidecar):
    with pytest.raises(lpq.LeanPqError, match="aggregation failed"):
        sidecar.aggregate()


@pytest.fixture
def directory():
    # Short: a Unix socket path holds at most 104 bytes on macOS.
    directory = tempfile.mkdtemp(prefix="lpq")
    yield directory
    shutil.rmtree(directory)


@needs_sidecar
def test_starts_and_stops_its_own_sidecar(sidecar, directory):
    key = lpq.XmssSecretKey.from_seed(b"\x07" * 32)
    message = b"\x33" * 32
    proof = sidecar.aggregate(xmss=[(key.public_key, message, key.sign(message, 0))])

    socket = os.path.join(directory, "s.sock")
    with lpq.Sidecar.start(env("LEANVM_SIDECAR_BIN"), socket, threads=2) as started:
        assert started.prover in ("experimental", "stable")
        started.verify(proof.to_bytes(), proof.xmss_claims)
    # Closing it stopped the sidecar, and a closed one refuses calls.
    with pytest.raises(lpq.LeanPqError, match="leanVM sidecar"):
        lpq.Sidecar.connect(socket)
    with pytest.raises(lpq.LeanPqError, match="closed"):
        started.verify(proof.to_bytes(), proof.xmss_claims)


@needs_sidecar
@pytest.mark.filterwarnings("ignore:This process .* is multi-threaded")
def test_a_forked_child_opens_its_own_connection(sidecar):
    key = lpq.XmssSecretKey.from_seed(b"\x08" * 32)
    message = b"\x44" * 32
    proof = sidecar.aggregate(xmss=[(key.public_key, message, key.sign(message, 0))])
    pid = os.fork()
    if pid == 0:
        # Whatever happens, the child must not return into pytest.
        code = 1
        try:
            sidecar.verify(proof.to_bytes(), proof.xmss_claims)
            code = 0
        finally:
            os._exit(code)
    # The parent's connection is untouched, and the child's verdict was its own.
    sidecar.verify(proof.to_bytes(), proof.xmss_claims)
    _, status = os.waitpid(pid, 0)
    assert os.waitstatus_to_exitcode(status) == 0
    with pytest.raises(lpq.LeanPqError, match="does not prove"):
        sidecar.verify(proof.to_bytes())


def test_connecting_where_no_sidecar_listens_fails(directory):
    match = "leanVM sidecar" if UNIX else "Unix sockets"
    with pytest.raises(lpq.LeanPqError, match=match):
        lpq.Sidecar.connect(os.path.join(directory, "none.sock"))
