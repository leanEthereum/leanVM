#!/usr/bin/env python3
"""Vendor NIST's ACVP ML-DSA sigVer vectors at one ACVP-Server commit.

    crates/ml_dsa_guest/tests/ml_dsa_guest/acvp/sync.py <acvp-server-commit>

Writes sigver.txt: every valid case and the first two of each rejection reason, per parameter
set, one line each, `<set> <tcId> <passed> <pk> <mu> <sig>` in hex. The guest takes mu, so mu is
computed here as ML-DSA.Verify forms it for the case's interface (pure, pre-hash, internal, or
external mu), with the standard library's hashes.
"""

import hashlib
import json
import pathlib
import sys
import urllib.request

PATH = "gen-val/json-files/ML-DSA-sigVer-FIPS204/internalProjection.json"
OID = {
    "SHA2-224": 4,
    "SHA2-256": 1,
    "SHA2-384": 2,
    "SHA2-512": 3,
    "SHA2-512/224": 5,
    "SHA2-512/256": 6,
    "SHA3-224": 7,
    "SHA3-256": 8,
    "SHA3-384": 9,
    "SHA3-512": 10,
    "SHAKE-128": 11,
    "SHAKE-256": 12,
}
PER_REASON = 2


def shake256(data: bytes, n: int) -> bytes:
    return hashlib.shake_256(data).digest(n)


def pre_hash(alg: str, msg: bytes) -> bytes:
    if alg == "SHAKE-128":
        return hashlib.shake_128(msg).digest(32)
    if alg == "SHAKE-256":
        return hashlib.shake_256(msg).digest(64)
    name = alg.replace("SHA2-512/", "sha512_").replace("SHA2-", "sha").replace("SHA3-", "sha3_")
    return hashlib.new(name, msg).digest()


def mu(group: dict, test: dict) -> bytes:
    if group.get("externalMu"):
        return bytes.fromhex(test["mu"])
    tr = shake256(bytes.fromhex(test["pk"]), 64)
    msg = bytes.fromhex(test["message"])
    if group["signatureInterface"] == "internal":
        return shake256(tr + msg, 64)
    ctx = bytes.fromhex(test["context"])
    if group["preHash"] == "pure":
        return shake256(tr + bytes([0, len(ctx)]) + ctx + msg, 64)
    oid = bytes([0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, OID[test["hashAlg"]]])
    return shake256(tr + bytes([1, len(ctx)]) + ctx + oid + pre_hash(test["hashAlg"], msg), 64)


def main() -> None:
    commit = sys.argv[1]
    url = f"https://raw.githubusercontent.com/usnistgov/ACVP-Server/{commit}/{PATH}"
    data = json.load(urllib.request.urlopen(url))
    lines, taken = [], {}
    for group in data["testGroups"]:
        name = group["parameterSet"].removeprefix("ML-DSA-")
        for test in group["tests"]:
            reason = test["reason"]
            key = (name, reason)
            if not test["testPassed"] and taken.get(key, 0) >= PER_REASON:
                continue
            taken[key] = taken.get(key, 0) + 1
            fields = [name, str(test["tcId"]), str(int(test["testPassed"])), test["pk"], mu(group, test).hex(), test["signature"]]
            lines.append(" ".join(fields).lower())
    here = pathlib.Path(__file__).parent
    (here / "sigver.txt").write_text("\n".join(lines) + "\n")
    (here / "COMMIT").write_text(commit + "\n")
    print(f"vendored ACVP-Server {commit}: {len(lines)} cases")


if __name__ == "__main__":
    main()
