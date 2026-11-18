#!/usr/bin/env python3
"""Fetches mainnet blocks for el-load, each with its execution witness (`debug_executionWitness`): the Merkle proofs
of every account and storage slot the block touches, the code it runs and the headers before it, as the reth node
serving the RPC produces it for its own stateless validation.

Usage: fetch-fixtures.py RPC_URLS OUT_DIR BLOCK_NUMBER...   (comma-separated RPCs serving debug_executionWitness,
tried in turn: a public one limits its free calls)
"""
import json
import sys
import time
import urllib.request


def rpc(urls, method, *params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": list(params)}).encode()
    for attempt in range(8 * len(urls)):
        url = urls[attempt % len(urls)]
        try:
            req = urllib.request.Request(url, body, {"content-type": "application/json", "user-agent": "el-load"})
            reply = json.load(urllib.request.urlopen(req, timeout=300))
            if "error" not in reply:
                return reply["result"]
            print(f"  {method} at {url}: {reply['error']}", file=sys.stderr)
        except Exception as e:  # a public endpoint drops or rate-limits now and then
            print(f"  {method} at {url}: {e}", file=sys.stderr)
        time.sleep(2 * (attempt // len(urls) + 1))
    sys.exit(f"{method} keeps failing")


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    urls, out = sys.argv[1].split(","), sys.argv[2]
    for number in map(int, sys.argv[3:]):
        block = rpc(urls, "eth_getBlockByNumber", hex(number), True)
        witness = rpc(urls, "debug_executionWitness", hex(number))
        with open(f"{out}/{number}.json", "w") as f:
            json.dump({"block": block, "witness": witness}, f, separators=(",", ":"))
        print(f"{out}/{number}.json: {len(block['transactions'])} transactions, {int(block['gasUsed'], 16):,} gas, "
              f"{len(witness['state'])} trie nodes")


main()
