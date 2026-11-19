#!/usr/bin/env python3
"""Fetches mainnet blocks for el-load, each with its execution witness as the reth node serving the RPC makes it.

Usage: fetch-fixtures.py RPC_URL OUT_DIR BLOCK_NUMBER...
"""
import json
import sys
import urllib.request


def rpc(url, method, *params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": list(params)}).encode()
    req = urllib.request.Request(url, body, {"content-type": "application/json", "user-agent": "el-load"})
    reply = json.load(urllib.request.urlopen(req, timeout=300))
    if "error" in reply:
        sys.exit(f"{method}: {reply['error']}")
    return reply["result"]


if len(sys.argv) < 4:
    sys.exit(__doc__)
url, out = sys.argv[1], sys.argv[2]
for number in sys.argv[3:]:
    block = rpc(url, "eth_getBlockByNumber", hex(int(number)), True)
    witness = rpc(url, "debug_executionWitness", hex(int(number)))
    with open(f"{out}/{number}.json", "w") as f:
        json.dump({"block": block, "witness": witness}, f, separators=(",", ":"))
    print(f"{out}/{number}.json")
