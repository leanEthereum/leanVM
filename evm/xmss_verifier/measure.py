#!/usr/bin/env python3
"""Measures the gas of an EIP-8483 add on anvil, with and without the leanXMSS proof of possession, for each scenario
and hardfork, and checks each transaction's gasUsed against its intrinsic gas, calldata floor and traced execution.

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
# Where the wrappers go, each with its contract in src/PossessionWrapper.sol.
WRAPPERS = {
    "C0": ("0x000000000000000000000000000000000000C000", "UncheckedWrapper"),
    "C": ("0x000000000000000000000000000000000000C001", "PossessionWrapper"),
}
PATHS = ["add", "C0", "C"]
VERIFIER = "0x000000000000000000000000000000000000B000"
SCENARIOS = ["S1", "S2", "S3"]
# Calldata gas per zero and nonzero byte: the standard cost, then the floor (EIP-7623, raised on Amsterdam).
CALLDATA = {"amsterdam": ((4, 16), (64, 64)), "osaka": ((4, 16), (10, 40))}
TRACE = {"disableStack": True, "disableMemory": True, "disableStorage": True}

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

    def receipt(self, tx, status=1):
        for _ in range(100):
            r = self.rpc("eth_getTransactionReceipt", tx)
            if r is not None:
                assert int(r["status"], 16) == status, r
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


def check_tampered(node, target, data):
    """An add whose signature has its last byte flipped reverts and changes none of the slots an add writes."""
    data = data[:-2] + f"{int(data[-2:], 16) ^ 1:02x}"
    slots = range(QUEUE_OFFSET + 3 * SLOTS_PER_ITEM)
    before = [node.storage(target, slot) for slot in slots]
    r = node.receipt(node.send(target, data, node.fee(target)), status=0)
    assert [node.storage(target, slot) for slot in slots] == before
    return r, data


def base_gas(node):
    """The intrinsic base of a contract call, without value and with 1 wei: the gasUsed of an empty call to a STOP."""
    stop = "0x000000000000000000000000000000000000BEEF"
    node.rpc("anvil_setCode", stop, "0x00")
    return [int(node.receipt(node.send(stop, "0x", value))["gasUsed"], 16) for value in (0, 1)]


def execution(node, tx, stack=False):
    """The gas the transaction's execution used, from its trace, and the trace's steps."""
    steps = node.rpc("debug_traceTransaction", tx, {**TRACE, "disableStack": not stack})["structLogs"]
    first, last = steps[0], steps[-1]
    # Below EIP-7825's transaction gas cap, EIP-8037 state gas comes out of the regular counter.
    assert first.get("stateGasReservoir", 0) == last.get("stateGasReservoir", 0) == 0
    assert last["refund"] == 0
    return first["gas"] - (last["gas"] - last["gasCost"]), steps


def breakdown(node, fork, base, receipt, data):
    """Splits a transaction's gasUsed into intrinsic gas and execution, or the floor, and checks the sum."""
    b = bytes.fromhex(data[2:])
    zeros, nonzeros = b.count(0), len(b) - b.count(0)
    (sz, snz), (fz, fnz) = CALLDATA[fork]
    intrinsic = base + sz * zeros + snz * nonzeros
    floor = base + fz * zeros + fnz * nonzeros
    exe, _ = execution(node, receipt["transactionHash"])
    gas_used = int(receipt["gasUsed"], 16)
    assert gas_used == max(intrinsic + exe, floor), (fork, gas_used, intrinsic, exe, floor)
    pays = "floor" if floor > intrinsic + exe else "standard"
    return dict(zeros=zeros, nonzeros=nonzeros, intrinsic=intrinsic, floor=floor, execution=exe, gas=gas_used, pays=pays)


def artifact(source, contract):
    with open(os.path.join(HERE, f"out/{source}/{contract}.json")) as f:
        return json.load(f)


def verify_breakdown(node, fork, base):
    """Splits the execution of a transaction calling B's verify on the fixture into its KECCAK256 opcodes, by input
    length, and everything else."""
    b = artifact("XmssVerifierB.sol", "XmssVerifierB")
    node.rpc("anvil_setCode", VERIFIER, b["deployedBytecode"]["object"])
    sig = FIXTURE["signature"][2:]
    data = "0x" + b["methodIdentifiers"]["verify(bytes32,bytes32,bytes)"] + FIXTURE["pq_data"][2:66]
    data += FIXTURE["message"][2:] + word(0x60)[2:] + word(len(sig) // 2)[2:] + sig + "0" * (-len(sig) % 64)
    r = node.receipt(node.send(VERIFIER, data, 0))
    tx = breakdown(node, fork, base, r, data)
    exe, steps = execution(node, r["transactionHash"], stack=True)
    assert node.rpc("debug_traceTransaction", r["transactionHash"], TRACE)["returnValue"].endswith("1")
    keccak = {}
    for step in steps:
        if step["op"] == "KECCAK256":
            # The stack is listed bottom first: offset on top, then the length.
            n, g = keccak.get(int(step["stack"][-2], 16), (0, 0))
            keccak[int(step["stack"][-2], 16)] = (n + 1, g + step["gasCost"])
    return dict(tx=tx, keccak=keccak, rest=exe - sum(g for _, g in keccak.values()))


def main():
    subprocess.run(["forge", "build", "--root", HERE], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    add = "0x" + FIXTURE["bls_pubkey"][2:] + FIXTURE["pq_data"][2:]
    assert len(add) == 2 + 2 * 112
    proof = add + FIXTURE["signature"][2:]
    bases, rows, verifies = {}, {}, {}
    for fork in FORKS:
        node = Anvil(fork)
        try:
            assert int(node.rpc("eth_chainId"), 16) == FIXTURE["chain_id"]
            bases[fork] = base_gas(node)
            # Every add sends 1 wei.
            base = bases[fork][1]
            node.rpc("anvil_setCode", PREDEPLOY, RUNTIME)
            targets = {"add": (PREDEPLOY, add)}
            for path, (address, contract) in WRAPPERS.items():
                node.rpc("anvil_setCode", address, artifact("PossessionWrapper.sol", contract)["deployedBytecode"]["object"])
                targets[path] = (address, proof)
            for path, (target, data) in targets.items():
                for scenario, r in scenarios(node, target, data).items():
                    rows[fork, path, scenario] = breakdown(node, fork, base, r, data)
            breakdown(node, fork, base, *check_tampered(node, WRAPPERS["C"][0], proof))
            verifies[fork] = verify_breakdown(node, fork, bases[fork][0])
        finally:
            node.close()

    for fork in FORKS:
        no_value, value = bases[fork]
        print(f"{fork}: base {value} for a call with 1 wei ({no_value} without value)")
        print(f"{'':9}{'zeros':>6}{'nonzero':>8}{'intrinsic':>10}{'floor':>8}{'execution':>10}{'gasUsed':>9}  pays")
        for path in PATHS:
            for scenario in SCENARIOS:
                r = rows[fork, path, scenario]
                print(
                    f"{path:4}{scenario:5}{r['zeros']:>6}{r['nonzeros']:>8}{r['intrinsic']:>10}{r['floor']:>8}"
                    f"{r['execution']:>10}{r['gas']:>9}  {r['pays']}"
                )
        print()

    print("B's verify of the fixture as a transaction: execution, its KECCAK256 opcodes by input length, the rest")
    print(f"{'':22}" + "".join(f"{fork:>10}" for fork in FORKS))
    v = verifies[FORKS[0]]
    print(f"{'gasUsed':22}" + "".join(f"{verifies[f]['tx']['gas']:>10}" for f in FORKS))
    print(f"{'pays':22}" + "".join(f"{verifies[f]['tx']['pays']:>10}" for f in FORKS))
    print(f"{'execution':22}" + "".join(f"{verifies[f]['tx']['execution']:>10}" for f in FORKS))
    total = sum(n for n, _ in v["keccak"].values())
    print(f"{f'KECCAK256 x{total}':22}" + "".join(f"{sum(g for _, g in verifies[f]['keccak'].values()):>10}" for f in FORKS))
    for size, (n, _) in sorted(v["keccak"].items()):
        print(f"{f'  {size} bytes x{n}':22}" + "".join(f"{verifies[f]['keccak'][size][1]:>10}" for f in FORKS))
    print(f"{'everything else':22}" + "".join(f"{verifies[f]['rest']:>10}" for f in FORKS))


if __name__ == "__main__":
    main()
