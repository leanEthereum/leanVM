"""Fetch the mainnet fixture: one finalized block's header, and `eth_getProof` of slot 0 of each account below at that block.

    python3 fetch.py https://ethereum-rpc.publicnode.com > mainnet.json

The header is RLP-encoded here from its JSON fields; the host's tests check that its keccak256 is the block hash.
"""

import json
import sys
import time
import urllib.request

ACCOUNTS = [
    "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2",  # WETH
    "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48",  # USDC
    "0xdAC17F958D2ee523a2206206994597C13D831ec7",  # USDT
    "0x6B175474E89094C44Da98b954EedeAC495271d0F",  # DAI
    "0xae7ab96520DE3A18E5e111B5EaAb095312D7fE84",  # stETH
    "0x7f39C581F595B53c5cb19bD0b3f8dA6c935E2Ca0",  # wstETH
    "0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599",  # WBTC
    "0x514910771AF9Ca656af840dff83E8264EcF986CA",  # LINK
    "0x1f9840a85d5aF5bf1D1762F925BDADdC4201F984",  # UNI
    "0x9f8F72aA9304c8B593d555F12eF6589cC3A579A2",  # MKR
    "0x95aD61b0a150d79219dCF64E1E6Cc01f0B64C4cE",  # SHIB
    "0x00000000219ab540356cBB839Cbe05303d7705Fa",  # beacon deposit contract
    "0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02",  # EIP-4788 beacon roots
    "0x0000F90827F1C53a10cb7A02335B175320002935",  # EIP-2935 block hashes
    "0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D",  # Uniswap V2 router
    "0xE592427A0AEce92De3Edee1F18E0157C05861564",  # Uniswap V3 router
    "0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2",  # Aave V3 pool
    "0xbEbc44782C7dB0a1A60Cb6fe97d0b483032FF1C7",  # Curve 3pool
    "0x00000000000C2E074eC69A0dFb2997BA6C7d2e1e",  # ENS registry
    "0x000000000022D473030F116dDEE9F6B43aC78BA3",  # Permit2
    "0x00000000006c3852cbEf3e08E8dF289169EdE581",  # Seaport 1.1
    "0x00000000000000ADc04C56Bf30aC9d3c0aAF14dC",  # Seaport 1.5
    "0x68b3465833fb72A70ecDF485E0e4C7bD8665Fc45",  # Uniswap SwapRouter02
    "0x1F98431c8aD98523631AE4a59f267346ea31F984",  # Uniswap V3 factory
    "0x5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f",  # Uniswap V2 factory
    "0x5f4eC3Df9cbd43714FE2740f5E3616155c5b8419",  # Chainlink ETH/USD
    "0xB8c77482e45F1F44dE1745F52C74426C631bDD52",  # BNB
    "0x4Fabb145d64652a948d72533023f6E7A623C7C53",  # BUSD
    "0x8E870D67F660D95d5be530380D0eC0bd388289E1",  # USDP
    "0x7D1AfA7B718fb893dB30A3aBc0Cfc608AaCfeBB0",  # MATIC
    "0x6982508145454Ce325dDbE47a25d4ec3d2311933",  # PEPE
    "0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045",  # an externally owned account: empty storage
]

SLOT = "0x" + "00" * 32

# The header's fields in RLP order, each a byte string or an integer (London through Prague).
HEADER = [
    ("parentHash", bytes),
    ("sha3Uncles", bytes),
    ("miner", bytes),
    ("stateRoot", bytes),
    ("transactionsRoot", bytes),
    ("receiptsRoot", bytes),
    ("logsBloom", bytes),
    ("difficulty", int),
    ("number", int),
    ("gasLimit", int),
    ("gasUsed", int),
    ("timestamp", int),
    ("extraData", bytes),
    ("mixHash", bytes),
    ("nonce", bytes),
    ("baseFeePerGas", int),
    ("withdrawalsRoot", bytes),
    ("blobGasUsed", int),
    ("excessBlobGas", int),
    ("parentBeaconBlockRoot", bytes),
    ("requestsHash", bytes),
]


def call(url, method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    request = urllib.request.Request(url, body, {"content-type": "application/json", "user-agent": "leanvm"})
    # Public endpoints rate-limit: retry a refused call after a pause.
    for _ in range(5):
        with urllib.request.urlopen(request) as response:
            reply = json.load(response)
        if "result" in reply:
            return reply["result"]
        print(reply, file=sys.stderr)
        time.sleep(2)
    sys.exit(f"{method} failed")


def rlp_length(length, offset):
    if length < 56:
        return bytes([offset + length])
    n = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(n)]) + n


def rlp_string(b):
    return b if len(b) == 1 and b[0] < 0x80 else rlp_length(len(b), 0x80) + b


def rlp_list(items):
    payload = b"".join(items)
    return rlp_length(len(payload), 0xC0) + payload


def field(value, kind):
    if kind is int:
        n = int(value, 16)
        return rlp_string(n.to_bytes((n.bit_length() + 7) // 8, "big"))
    return rlp_string(bytes.fromhex(value[2:]))


def main():
    url = sys.argv[1]
    block = call(url, "eth_getBlockByNumber", ["finalized", False])
    header = rlp_list([field(block[name], kind) for name, kind in HEADER])
    proofs = [call(url, "eth_getProof", [account, [SLOT], block["number"]]) for account in ACCOUNTS]
    fixture = {"number": int(block["number"], 16), "hash": block["hash"], "header": "0x" + header.hex(), "proofs": proofs}
    json.dump(fixture, sys.stdout, indent=1)
    print()


main()
