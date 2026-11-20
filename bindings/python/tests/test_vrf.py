"""The VRF tree, against a pinned root."""

import py_lean_pq as lpq
import pytest

SEED = b"\x09" * 32
ROOT = bytes.fromhex("af45ef4aca47606c0e6722dc71af01e3f13df93253e6aec5805eb1e8ed3bb0fa")


def test_reproduces_the_known_root():
    key = lpq.VrfKey.from_seed(SEED, 100, 200)
    assert key.root() == ROOT

    proof = key.proof(150)
    assert len(proof) == 1024
    assert lpq.vrf_verify(ROOT, 150, proof) is None
    with pytest.raises(lpq.LeanPqError, match="slot 151"):
        lpq.vrf_verify(ROOT, 151, proof)
    for slot in (100, 151, 199):
        lpq.vrf_verify(ROOT, slot, key.proof(slot))


def test_loads_a_key_from_its_cache():
    cache = lpq.VrfKey.from_seed(SEED, 100, 200).cache_to_bytes()

    loaded = lpq.VrfKey.from_cache_bytes(SEED, cache, ROOT)
    assert loaded.cache_to_bytes() == cache
    lpq.vrf_verify(ROOT, 150, loaded.proof(150))

    with pytest.raises(ValueError, match="VRF cache is malformed"):
        lpq.VrfKey.from_cache_bytes(SEED, cache[:-1], ROOT)
    with pytest.raises(ValueError, match="does not match the root"):
        lpq.VrfKey.from_cache_bytes(SEED, cache, bytes(32))
    with pytest.raises(ValueError, match="seed must be exactly 32 bytes"):
        lpq.VrfKey.from_cache_bytes(SEED[:31], cache, ROOT)


def test_rejects_bad_ranges_slots_and_lengths():
    with pytest.raises(lpq.LeanPqError, match="empty"):
        lpq.VrfKey.from_seed(SEED, 5, 5)
    with pytest.raises(lpq.LeanPqError, match="past 2\\^31"):
        lpq.VrfKey.from_seed(SEED, 0, 2**31 + 1)
    with pytest.raises(ValueError, match="seed must be exactly 32 bytes"):
        lpq.VrfKey.from_seed(SEED[:31], 100, 200)

    key = lpq.VrfKey.from_seed(SEED, 100, 200)
    for slot in (99, 200):
        with pytest.raises(lpq.LeanPqError, match="outside the key's range"):
            key.proof(slot)
    with pytest.raises(ValueError, match="proof must be exactly 1024 bytes"):
        lpq.vrf_verify(ROOT, 150, key.proof(150)[:-1])
