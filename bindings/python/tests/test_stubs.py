import pathlib
import shutil
import subprocess
import sys

import pytest


def test_stubs_match_runtime():
    if shutil.which("mypy") is None:
        pytest.skip("mypy not installed")
    project_root = pathlib.Path(__file__).resolve().parent.parent
    allowlist = project_root / "stubtest_allowlist.txt"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "mypy.stubtest",
            "py_lean_pq",
            "--allowlist",
            str(allowlist),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"mypy.stubtest failed:\n--- stdout ---\n{result.stdout}\n"
        f"--- stderr ---\n{result.stderr}"
    )
