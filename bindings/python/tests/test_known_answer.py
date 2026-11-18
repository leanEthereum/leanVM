"""leanSPHINCS known answers shared with the Rust bindings, EthLib and leanVM."""

from pathlib import Path

import py_lean_pq as lpq
import pytest

FIXTURES = Path(__file__).resolve().parents[2] / "rust" / "tests" / "fixtures"

SEED = bytes((37 * i + 11) % 256 for i in range(32))
MESSAGE = bytes((7 * i + 3) % 256 for i in range(32))


def fixture(name: str) -> tuple[bytes, bytes]:
    """Return the public key and signature of a fixture, one hex line each."""
    public_key, signature = (FIXTURES / name).read_text().split()
    return bytes.fromhex(public_key), bytes.fromhex(signature)


def test_reproduces_the_known_answer():
    public_key, signature = fixture("lean_sphincs_known_answer.hex")
    key = lpq.SphincsSecretKey.from_seed(SEED)
    assert key.public_key == public_key
    assert key.sign(MESSAGE) == signature
    assert lpq.sphincs_verify(public_key, MESSAGE, signature) is None


def test_rejects_the_previous_layout():
    public_key, signature = fixture("lean_sphincs_pre_fips205.hex")
    assert lpq.SphincsSecretKey.from_seed(SEED).public_key != public_key
    with pytest.raises(lpq.LeanPqError):
        lpq.sphincs_verify(public_key, MESSAGE, signature)
