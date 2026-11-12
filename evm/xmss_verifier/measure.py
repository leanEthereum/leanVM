#!/usr/bin/env python3
"""Prints every number of the leanXMSS verifier's gas measurement, on Amsterdam and Osaka: verify alone, from the
forge snapshot test, then on anvil an EIP-8483 add with and without the proof of possession in each scenario, each
transaction's gasUsed checked against its intrinsic gas, calldata floor and traced execution, the split of B's verify
and the cost of the message.

Run from anywhere, with forge and anvil on the PATH: `python3 evm/xmss_verifier/measure.py`.
"""

import hashlib
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
SIGNING_ROOT = "0x000000000000000000000000000000000000D000"
SCENARIOS = {
    "S1": "the first request ever",
    "S2": "the first request of a block, on a queue used before",
    "S3": "a later request in the same block",
}
GWEI = [1, 5, 20]
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
    return dict(
        hash=receipt["transactionHash"],
        zeros=zeros,
        nonzeros=nonzeros,
        intrinsic=intrinsic,
        floor=floor,
        execution=exe,
        gas=gas_used,
        pays=pays,
    )


def message_gas(node, tx):
    """The gas C spends computing M, from loading the free memory pointer before CHAINID to the KECCAK256 over 112
    bytes, whose output must be the fixture's message."""
    _, steps = execution(node, tx, stack=True)
    i = next(k for k, step in enumerate(steps) if step["op"] == "CHAINID")
    j = next(k for k in range(i, len(steps)) if steps[k]["op"] == "KECCAK256")
    assert [step["op"] for step in steps[i - 2 : i]] == ["PUSH1", "MLOAD"] and int(steps[j]["stack"][-2], 16) == 112
    assert int(steps[j + 1]["stack"][-1], 16) == int(FIXTURE["message"], 16)
    return sum(step["gasCost"] for step in steps[i - 2 : j + 1])


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


def signing_root_gas(node, add):
    """The gas of computing EIP-8450's signing root instead of M, measured on test/SigningRoot.sol: from loading the
    free memory pointer to the success check of the third SHA-256 call, the same span as M's."""
    a = artifact("SigningRoot.sol", "SigningRoot")
    node.rpc("anvil_setCode", SIGNING_ROOT, a["deployedBytecode"]["object"])
    r = node.receipt(node.send(SIGNING_ROOT, add, 0))
    _, steps = execution(node, r["transactionHash"], stack=True)
    i = next(k for k, step in enumerate(steps) if step["op"] == "MLOAD")
    calls = [k for k, step in enumerate(steps) if step["op"] == "STATICCALL"]
    j = next(k for k in range(calls[-1], len(steps)) if steps[k]["op"] == "JUMPI")
    assert steps[i - 1]["op"] == "PUSH1" and int(steps[i]["stack"][-1], 16) == 0x40 and len(calls) == 3
    sha = lambda b: hashlib.sha256(b).digest()
    b = bytes.fromhex(add[2:])
    domain = bytes.fromhex("13000000" + "ee" * 28)
    root = sha(sha(sha(b[:48] + bytes(16)) + b[48:80]) + domain)
    assert node.rpc("debug_traceTransaction", r["transactionHash"], TRACE)["returnValue"].removeprefix("0x") == root.hex()
    return sum(step["gasCost"] for step in steps[i - 1 : j + 1] if step["op"] != "STATICCALL") + sum(
        steps[k]["gas"] - steps[k + 1]["gas"] for k in calls
    )


def snapshots():
    """Runs the verify gas test on each hardfork and returns, per hardfork, verifier and kind, the min and max over the
    valid vectors of its snapshot."""
    out = {}
    for fork in FORKS:
        cmd = ["forge", "test", "--root", HERE, "--isolate", "--hardfork", fork, "--match-contract", "VerifyGasTest"]
        subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        with open(os.path.join(HERE, f"snapshots/verify-{fork}.json")) as f:
            snap = json.load(f)
        for name, value in snap.items():
            verifier, kind, _ = name.split()
            lo, hi = out.get((fork, verifier, kind), (None, None))
            v = int(value)
            out[fork, verifier, kind] = (v if lo is None else min(lo, v), v if hi is None else max(hi, v))
    return out


def main():
    subprocess.run(["forge", "build", "--root", HERE], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    snaps = snapshots()
    print("verify alone, min and max over the 4 valid vectors: a transaction calling it, and its execution")
    print(f"{'':16}" + "".join(f"{fork:>20}" for fork in FORKS))
    for verifier in "AB":
        for kind in ["transaction", "execution"]:
            print(f"{verifier + ' ' + kind:16}" + "".join(f"{'%d to %d' % snaps[f, verifier, kind]:>20}" for f in FORKS))
    print()
    add = "0x" + FIXTURE["bls_pubkey"][2:] + FIXTURE["pq_data"][2:]
    assert len(add) == 2 + 2 * 112
    proof = add + FIXTURE["signature"][2:]
    bases, rows, verifies, messages, roots = {}, {}, {}, {}, {}
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
            messages[fork] = message_gas(node, rows[fork, "C", "S1"]["hash"])
            roots[fork] = signing_root_gas(node, add)
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
    print()

    print("The message: M in C, against EIP-8450's signing root in test/SigningRoot.sol")
    print(f"{'':22}" + "".join(f"{fork:>10}" for fork in FORKS))
    print(f"{'M':22}" + "".join(f"{messages[f]:>10}" for f in FORKS))
    print(f"{'signing root':22}" + "".join(f"{roots[f]:>10}" for f in FORKS))

    for scenario, title in SCENARIOS.items():
        print()
        print(f"{scenario}, {title}")
        print(f"{'':36}" + "".join(f"{fork:>12}" for fork in FORKS))
        gas = {(f, p): rows[f, p, scenario]["gas"] for f in FORKS for p in PATHS}
        exe = {(f, p): rows[f, p, scenario]["execution"] for f in FORKS for p in PATHS}
        lines = [
            ("add without the proof", lambda f: gas[f, "add"]),
            ("C0, the proof unchecked", lambda f: gas[f, "C0"]),
            ("C, the proof checked", lambda f: gas[f, "C"]),
            ("C - add", lambda f: gas[f, "C"] - gas[f, "add"]),
            ("C0 - add", lambda f: gas[f, "C0"] - gas[f, "add"]),
            ("C - C0", lambda f: gas[f, "C"] - gas[f, "C0"]),
            ("C - C0 in execution", lambda f: exe[f, "C"] - exe[f, "C0"]),
        ]
        for label, value in lines:
            print(f"{label:36}" + "".join(f"{value(f):>12}" for f in FORKS))
        for path, label in [("add", "without"), ("C", "with")]:
            for gwei in GWEI:
                eth = lambda f: f"{gas[f, path] * gwei / 1e9:.6f}"
                print(f"{f'ETH {label} the proof at {gwei} gwei':36}" + "".join(f"{eth(f):>12}" for f in FORKS))


if __name__ == "__main__":
    main()
