#!/usr/bin/env python3
"""Fetches mainnet blocks for el-load to re-execute: each block with its transactions, its pre-state (every account,
storage slot and code its transactions touch, as `prestateTracer` reports them), the 256 block hashes BLOCKHASH can
read, and each transaction's gas used, which el-load's replay must match.

Usage: fetch-fixtures.py RPC_URL OUT_DIR BLOCK_NUMBER...   (the RPC must serve debug_traceBlockByNumber)
"""
import json
import sys
import time
import urllib.request


def rpc(url, method, *params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": list(params)}).encode()
    for attempt in range(8):
        try:
            req = urllib.request.Request(url, body, {"content-type": "application/json", "user-agent": "el-load"})
            reply = json.load(urllib.request.urlopen(req, timeout=120))
            if "error" not in reply:
                return reply["result"]
            print(f"  {method}: {reply['error']}", file=sys.stderr)
        except Exception as e:  # a public endpoint drops or rate-limits now and then
            print(f"  {method}: {e}", file=sys.stderr)
        time.sleep(2 * (attempt + 1))
    sys.exit(f"{method} keeps failing")


def fetch(url, number):
    block = rpc(url, "eth_getBlockByNumber", hex(number), True)
    receipts = rpc(url, "eth_getBlockReceipts", hex(number))
    traces = rpc(url, "debug_traceBlockByNumber", hex(number), {"tracer": "prestateTracer"})
    diffs = rpc(url, "debug_traceBlockByNumber", hex(number), {"tracer": "prestateTracer", "tracerConfig": {"diffMode": True}})
    # Accounts the block creates, by the transaction that creates them: a later transaction's trace shows them created,
    # which is no part of the block's pre-state.
    created = {}
    for i, diff in enumerate(diffs):
        for address in diff["result"]["post"].keys() - diff["result"]["pre"].keys():
            created.setdefault(address, i)
    # The block's pre-state: each account as the first transaction that touched it found it (the tracer leaves out a
    # zero balance or nonce and empty code, so a later trace must not fill them in), and each storage slot likewise.
    prestate = {}
    for i, trace in enumerate(traces):
        for address, account in trace["result"].items():
            if created.get(address, i) < i:
                continue
            if address not in prestate:
                prestate[address] = {
                    "balance": account.get("balance", "0x0"),
                    "nonce": account.get("nonce", 0),
                    "code": account.get("code", "0x"),
                    "storage": {},
                }
            for slot, word in account.get("storage", {}).items():
                prestate[address]["storage"].setdefault(slot, word)
    # The tracer leaves out code reached only through an EIP-7702 delegation: add each delegation's target, as the
    # parent block left it. Its storage is not needed, as delegated code runs on the delegating account's.
    targets = {a["address"] for tx in block["transactions"] for a in tx.get("authorizationList", [])}
    targets |= {"0x" + a["code"][8:48] for a in prestate.values() if a["code"].startswith("0xef0100")}
    parent = hex(number - 1)
    for target in sorted(targets - prestate.keys()):
        prestate[target] = {
            "balance": rpc(url, "eth_getBalance", target, parent),
            "nonce": int(rpc(url, "eth_getTransactionCount", target, parent), 16),
            "code": rpc(url, "eth_getCode", target, parent),
            "storage": {},
        }
    hashes = {}
    for ancestor in range(max(0, number - 256), number):
        hashes[hex(ancestor)] = rpc(url, "eth_getBlockByNumber", hex(ancestor), False)["hash"]
    return {
        "block": block,
        "gas_used": [r["gasUsed"] for r in receipts],
        "status": [r["status"] for r in receipts],
        "prestate": prestate,
        "block_hashes": hashes,
    }


def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    url, out = sys.argv[1], sys.argv[2]
    for number in map(int, sys.argv[3:]):
        fixture = fetch(url, number)
        path = f"{out}/{number}.json"
        with open(path, "w") as f:
            json.dump(fixture, f, separators=(",", ":"))
        block = fixture["block"]
        print(f"{path}: {len(block['transactions'])} transactions, {int(block['gasUsed'], 16):,} gas")


main()
