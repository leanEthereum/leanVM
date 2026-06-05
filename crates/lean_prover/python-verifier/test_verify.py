"""Pure-Python verifier for leanVM proofs (the verification spec — `test_verify.py` is the runner).
Setup the test vectors (one-time):
    cargo test --release --package lean_prover --lib -- test_zkvm::dump_test_vectors_for_python_verifier --include-ignored
Run (verifies every dumped vector):
    python3 crates/lean_prover/python-verifier/test_verify.py
Format:
    ruff format --line-length 150 crates/lean_prover/python-verifier
"""

from __future__ import annotations
import array
import json
import sys
from pathlib import Path

from verifier import *

VECTORS_DIR = Path(__file__).resolve().parents[3] / "target" / "zkvm_test_vectors"


def load_proof(proof_json_path: Path) -> tuple[list[int], list[Fp], Proof]:
    raw = json.loads(proof_json_path.read_text())
    arr = array.array("I")
    arr.frombytes((proof_json_path.parent / raw["bytecode_multilinear_path"]).read_bytes())
    bytecode_multilinear: list[int] = list(arr)
    fp_list = lambda xs: [Fp(v) for v in xs]
    public_input = fp_list(raw["public_input"])
    proof = Proof(
        transcript=fp_list(raw["proof"]["transcript"]),
        merkle_openings=[
            MerkleOpening(leaf_data=fp_list(o["leaf_data"]), path=[fp_list(d) for d in o["path"]]) for o in raw["proof"]["merkle_openings"]
        ],
    )
    return bytecode_multilinear, public_input, proof


def load_manifest() -> list[dict]:
    manifest_path = VECTORS_DIR / "manifest.json"
    assert manifest_path.exists(), f"Manifest not found at {manifest_path}. Generate the test vectors first (see verifier.py)."
    return json.loads(manifest_path.read_text())["vectors"]


def verify_vector(entry: dict) -> None:
    """Load and verify a single vector; raises on any failure."""
    bytecode_multilinear, public_input, proof = load_proof(VECTORS_DIR / entry["dir"] / "proof.json")
    verify_execution(bytecode_multilinear, public_input, proof)


def test_verify_all_vectors() -> None:
    """Verify every dumped vector (usable as a pytest test: raises on the first failure)."""
    vectors = load_manifest()
    assert vectors, "no vectors listed in manifest"
    for entry in vectors:
        verify_vector(entry)


def _config_str(entry: dict) -> str:
    # Meta params come from the manifest (emitted by the Rust prover); `verify_execution`
    # itself stays a pure verify-or-raise and re-derives everything from the proof.
    heights = "  ".join(f"{table}={h}" for table, h in entry["table_log_heights"].items())
    return f"rate={entry['log_inv_rate']}  log_memory={entry['log_memory']:<3}  bytecode={entry['bytecode_log_size']:<3}  {heights}"


def main() -> int:
    vectors = load_manifest()
    print(f"Verifying {len(vectors)} proof(s) from {VECTORS_DIR}\n")
    n_failed = 0
    for entry in vectors:
        label = f"vector {entry['dir']}"
        try:
            verify_vector(entry)
            print(f"  OK  {label:<12} {_config_str(entry)}")
        except Exception as e:
            n_failed += 1
            print(f"  KO  {label:<12} {_config_str(entry)}  FAILED: {e}")
    print()
    if n_failed:
        print(f"{n_failed}/{len(vectors)} proof(s) FAILED")
        return 1
    print(f"All {len(vectors)} proof(s) successfully verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
