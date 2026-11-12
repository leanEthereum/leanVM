# xmss_verifier

What it costs in gas to verify a leanXMSS signature in an EVM contract, measured for the [EIP-8483](https://github.com/ethereum/EIPs/pull/12609) discussion of whether the PQ registration predeploy could check a proof of possession itself: the signature travels in calldata, the contract verifies it, and it is neither stored nor forwarded to the consensus layer. It lives outside the Cargo workspace. The numbers are in the commit messages, and this script prints all of them:

```sh
python3 evm/xmss_verifier/measure.py   # every number as tables, on Amsterdam and Osaka (needs forge and anvil)
cd evm/xmss_verifier && forge test     # the vectors and the verify gas snapshots
```

## Verifiers

`src/XmssVerifierA.sol` is plain Solidity, and `src/XmssVerifierB.sol` builds each hash input in place in assembly. Both expose `verify(bytes32 publicKey, bytes32 message, bytes calldata signature)` and follow `crates/signatures/src/lean_xmss` byte for byte. `test/XmssVerifier.t.sol` runs them on EthLib's leanXMSS verify vectors, vendored in `crates/signatures/tests/signatures/ethlib/xmss/verify`. A null output, for an input of the wrong length, counts as false, which is what EIP-8450's `xmss.Verify` returns. The two cases with a short public key or message can't be passed as `bytes32`, and `test/Vectors.t.sol` checks they are the only ones; the other 21 go through `verify`.

## Toolchain

solc 0.8.38, with the optimizer on at 200 runs and via-IR off, compiling for Osaka (`evm_version`): this solc offers Amsterdam only as experimental, and the code uses no opcode Amsterdam adds. Tests and anvil run the Amsterdam gas schedule as Foundry 1.9.0 implements it (`hardfork` in `foundry.toml`, `anvil --hardfork amsterdam`). Amsterdam isn't final and its repricings land on exactly what this measures, so every table also has an Osaka column, the schedule live today. forge-std 1.17.0 comes through soldeer.

## What Amsterdam changes here

Foundry 1.9.0 runs Amsterdam as revm v120 defines it, the Glamsterdam devnet-8 schedule. The changes that move the numbers here are:

- [EIP-2780](https://eips.ethereum.org/EIPS/eip-2780) splits the intrinsic base into a smaller transaction base, a cold access to the recipient and a charge for sending value. A call without value gets cheaper, but the adds send the 1-wei fee and pay the same base as on Osaka. A transfer that creates an account also pays state gas.
- [EIP-7976](https://eips.ethereum.org/EIPS/eip-7976) raises the calldata floor and charges zero bytes like nonzero ones, on top of EIP-2780's base. The standard calldata cost stays the same.
- [EIP-8037](https://eips.ethereum.org/EIPS/eip-8037) charges state gas for new state at a fixed cost per byte, so writing a nonzero value to a zero slot costs several times more. That is most of the add's cost in S1, and the cost of the tail write in S2. Below [EIP-7825](https://eips.ethereum.org/EIPS/eip-7825)'s transaction gas cap, state gas comes out of the regular gas, and the receipt's gasUsed counts it.
- [EIP-8038](https://eips.ethereum.org/EIPS/eip-8038) raises the cost of a storage write that changes a slot, and of a cold account access, which the wrapper's DELEGATECALL pays.
- [EIP-7708](https://eips.ethereum.org/EIPS/eip-7708) has every ETH transfer, the fee included, emit a log from the system address. The log costs no gas of its own.

KECCAK256, memory, calldata copies, LOG, CHAINID and the SHA-256 precompile cost the same as on Osaka, so verify's execution is the same on both.

## What is measured

`test/VerifyGas.t.sol` measures verify alone. It calls each verifier on the 4 valid vectors and snapshots, in `snapshots/verify-<hardfork>.json`, the gasUsed of a transaction making the call, with its intrinsic gas or calldata floor, and the execution of the call alone, ABI decoding included. Forge runs a test's call as its own transaction only under isolation, which Foundry 1.9.0 turns on by default, and only for a CALL. `verify` is view, so the test calls it with a low-level call, and it skips without isolation.

`measure.py` measures the add. It starts anvil for each hardfork and places the EIP-8483 runtime bytecode with `anvil_setCode`, at an address of its own since the EIP's is still to be chosen. The bytecode, `test/fixtures/eip8483.hex`, is from ethereum/EIPs PR #12609 at 20e8d373, and geas v0.3.3 reproduces it from the PR's `main.eas`. The script sends the 112-byte input of `test/fixtures/registration.json`, a BLS public key and pq_data, each time with the fee the contract's getter returns, in three scenarios:

- S1 is the first request ever, on zero storage.
- S2 is the first request of a block on a queue used before: queue slots nonzero, head and tail 0, and the count and last block from the previous block.
- S3 is a second request in S2's block, so tail, count and last block hold what S2 wrote.

Each add has to log its 132-byte record and move the tail.

The wrappers in `src/PossessionWrapper.sol` add the proof. Their fallback takes the 112-byte input followed by a 2404-byte signature, checks the signature, then DELEGATECALLs the EIP-8483 bytecode with the input. DELEGATECALL keeps the caller, the value and the storage, so the add is the geas code itself, which reads no ADDRESS or SELFBALANCE that would see the wrapper. C (`PossessionWrapper`) requires leaf index 0 and B's verify of the message below. C0 (`UncheckedWrapper`) checks nothing, so C0 against the plain add is the cost of the extra calldata and the wrapper, and C against C0 the cost of checking the proof, where neither pays the calldata floor. The scenarios run on each wrapper's own storage, and a signature with a flipped byte has to revert and leave the storage as it was.

For every transaction, the script traces the execution and checks that gasUsed is the larger of the intrinsic gas plus the execution and the calldata floor. The intrinsic base comes from an empty call carrying 1 wei, like every add. The script also splits the execution of a transaction calling B's verify into its KECCAK256 opcodes, by input length, and the rest.

## The message

C checks a signature at leaf index 0 of `M = keccak256(chainid | bls_pubkey | xmss_public_key)`, with the chain ID as a 32-byte word. EIP-8450 signs the SSZ signing root of `PQKeyPossession(pubkey, xmss_public_key)` instead, under a domain derived from the network's genesis fork version and genesis validators root. Checking that in the contract takes three SHA-256 precompile calls and puts those constants in the bytecode, so the bytecode, and with the EIP-7997 CREATE2 factory the address, would differ per network. M reads the chain ID at runtime, so one bytecode serves every network. Leaf 0 is a one-time key and can't sign both messages, so using M means proposing that EIP-8450's possession message become M. That fits the design measured here, where the execution layer checks the signature and the consensus layer never sees it.

To price the alternative, `test/SigningRoot.sol` computes EIP-8450's signing root with a placeholder domain. The script checks its output against SSZ computed in Python, and measures it over the same span of code as M. That measures this sketch, not a predeploy, so treat its difference with M as an estimate.

## Fixtures

`gen/` is a Cargo package outside the workspace, with path dependencies on `crates/signatures` and `crates/primitives`. In it, `cargo run --release -- fixture` writes `test/fixtures/registration.json`: a fixed BLS public key, a leanXMSS key from a fixed seed, pq_data as that key then 32 bytes standing in for the VRF root, and the key's signature of M at leaf index 0 for chain ID 31337, the default of forge and anvil. `cargo run --release -- trace` prints the intermediate values of verifying the first-leaf vector.
