#!/usr/bin/env python3
"""Measures the gas of an EIP-8483 add on anvil, for each scenario and hardfork.

Run from anywhere, with anvil on the PATH: `python3 evm/xmss_verifier/measure.py`.
"""

import json
import os
import socket
import subprocess
import time
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
FORKS = ["amsterdam", "osaka"]
# EIP-8483 leaves the predeploy address to be chosen.
PREDEPLOY = "0x0000000000000000000000000000000000008483"
RUNTIME = open(os.path.join(HERE, "test/fixtures/eip8483.hex")).read().strip()
FIXTURE = json.load(open(os.path.join(HERE, "test/fixtures/registration.json")))

SLOT_EXCESS, SLOT_COUNT, SLOT_HEAD, SLOT_TAIL, SLOT_LAST_BLOCK, QUEUE_OFFSET = range(6)
SLOTS_PER_ITEM = 5


def word(n):
    return "0x" + n.to_bytes(32, "big").hex()


class Anvil:
    def __init__(self, fork):
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            self.port = s.getsockname()[1]
        self.proc = subprocess.Popen(
            ["anvil", "--hardfork", fork, "--port", str(self.port), "--steps-tracing"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        for _ in range(100):
            try:
                self.sender = self.rpc("eth_accounts")[0]
                return
            except OSError:
                time.sleep(0.1)
        raise RuntimeError("anvil did not start")

    def close(self):
        self.proc.terminate()
        self.proc.wait()

    def rpc(self, method, *params):
        body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
        req = urllib.request.Request(f"http://127.0.0.1:{self.port}", body, {"Content-Type": "application/json"})
        res = json.load(urllib.request.urlopen(req))
        if "error" in res:
            raise RuntimeError(f"{method}: {res['error']}")
        return res["result"]

    def storage(self, address, slot):
        return int(self.rpc("eth_getStorageAt", address, hex(slot), "latest"), 16)

    def fee(self, target):
        """The EIP-8483 fee getter, run on `target`'s storage."""
        return int(self.rpc("eth_call", {"to": target, "data": "0x"}, "latest", {target: {"code": RUNTIME}}), 16)

    def send(self, to, data, value):
        """Sends a transaction and returns its hash; the caller mines it."""
        tx = {"from": self.sender, "to": to, "data": data, "value": hex(value), "gas": hex(3_000_000)}
        return self.rpc("eth_sendTransaction", tx)

    def receipt(self, tx):
        for _ in range(100):
            r = self.rpc("eth_getTransactionReceipt", tx)
            if r is not None:
                assert r["status"] == "0x1", r
                return r
            time.sleep(0.05)
        raise RuntimeError(f"{tx} was not mined")


def scenarios(node, target, data):
    """Sends the adds of S1, S2 and S3 to `target`, whose storage starts zero, and returns their receipts.

    S1 is the first request ever. S2 is the first request of a block on a queue used before, and S3 the request after
    it in the same block, so one block carries both.
    """
    s1 = node.receipt(node.send(target, data, node.fee(target)))
    check_landed(node, target, data, [s1], 1)
    head = int(node.rpc("eth_blockNumber"), 16)
    slots = {SLOT_EXCESS: 0, SLOT_COUNT: 3, SLOT_HEAD: 0, SLOT_TAIL: 0, SLOT_LAST_BLOCK: head}
    for slot in range(QUEUE_OFFSET, QUEUE_OFFSET + 2 * SLOTS_PER_ITEM):
        slots[slot] = int("ee" * 32, 16)
    for slot, value in slots.items():
        node.rpc("anvil_setStorageAt", target, word(slot), word(value))
    node.rpc("evm_setAutomine", False)
    fee = node.fee(target)
    txs = [node.send(target, data, fee) for _ in range(2)]
    node.rpc("evm_mine")
    node.rpc("evm_setAutomine", True)
    s2, s3 = [node.receipt(tx) for tx in txs]
    assert s2["blockNumber"] == s3["blockNumber"] and int(s3["transactionIndex"], 16) == 1
    check_landed(node, target, data, [s2, s3], 2)
    return {"S1": s1, "S2": s2, "S3": s3}


def check_landed(node, target, data, receipts, tail):
    """Each add logged its 132-byte record from `target`, and the queue tail moved."""
    record = "0x" + node.sender[2:].lower() + data[2:226]
    for r in receipts:
        # Amsterdam also logs the fee's transfer from the system address (EIP-7708).
        [log] = [log for log in r["logs"] if log["address"].lower() == target.lower()]
        assert log["topics"] == [] and log["data"] == record, log
    assert node.storage(target, SLOT_TAIL) == tail


def main():
    data = "0x" + FIXTURE["bls_pubkey"][2:] + FIXTURE["pq_data"][2:]
    assert len(data) == 2 + 2 * 112
    gas = {}
    for fork in FORKS:
        node = Anvil(fork)
        try:
            node.rpc("anvil_setCode", PREDEPLOY, RUNTIME)
            for scenario, r in scenarios(node, PREDEPLOY, data).items():
                gas[fork, scenario] = int(r["gasUsed"], 16)
        finally:
            node.close()
    print("gasUsed of an add without the proof")
    print(f"{'':10}" + "".join(f"{fork:>12}" for fork in FORKS))
    for scenario in ["S1", "S2", "S3"]:
        print(f"{scenario:10}" + "".join(f"{gas[fork, scenario]:>12}" for fork in FORKS))


if __name__ == "__main__":
    main()
