"""leanSPHINCS known answers, shared with EthLib and `crates/lean_sphincs`."""

from pathlib import Path

import py_lean_pq as lpq
import pytest

ROOT = Path(__file__).resolve().parents[3]
KNOWN_ANSWER = ROOT / "crates" / "lean_sphincs" / "tests" / "lean_sphincs" / "known_answer.hex"
PRE_FIPS205 = ROOT / "bindings" / "rust" / "tests" / "fixtures" / "lean_sphincs_pre_fips205.hex"

SEED = bytes((37 * i + 11) % 256 for i in range(32))
MESSAGE = bytes((7 * i + 3) % 256 for i in range(32))


def fixture(path: Path) -> tuple[bytes, bytes]:
    """Return the public key and signature of a fixture, one hex line each."""
    public_key, signature = path.read_text().split()
    return bytes.fromhex(public_key), bytes.fromhex(signature)


def test_reproduces_the_known_answer():
    public_key, signature = fixture(KNOWN_ANSWER)
    key = lpq.SphincsSecretKey.from_seed(SEED)
    assert key.public_key == public_key
    assert key.sign(MESSAGE) == signature
    assert lpq.sphincs_verify(public_key, MESSAGE, signature) is None


def test_rejects_the_previous_layout():
    public_key, signature = fixture(PRE_FIPS205)
    assert lpq.SphincsSecretKey.from_seed(SEED).public_key != public_key
    with pytest.raises(lpq.LeanPqError):
        lpq.sphincs_verify(public_key, MESSAGE, signature)
