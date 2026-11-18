# el-load

An execution client's load, to run next to the prover (`bench/bench-alongside-el.sh`). It validates real mainnet blocks as a stateless [reth](https://github.com/paradigmxyz/reth) node does, a slot's worth of gas per slot, spread over parallel workers the way block-level access lists (EIP-7928, Glamsterdam) let a client spread one block's transactions.

Validating a block (`reth_stateless::stateless_validation`) is a node's whole work on it but for reading a database: it verifies every transaction's signature, verifies the witness (the Merkle proofs of everything the block touches) against the parent's state root, executes the block, checks its receipts and gas, and recomputes the state root, which must be the block's.

```bash
cargo build --release --manifest-path bench/el-load/Cargo.toml
bench/el-load/target/release/el-load check bench/el-load/fixtures
bench/el-load/target/release/el-load run bench/el-load/fixtures --gas-per-slot 200000000 --slot-ms 12000 --workers 4
```

- `check` validates each block once.
- `run` prints each slot's gas and wall time, until killed or after `--slots N`. `--slot-ms 0` runs the slots back to back.

The defaults, 200M gas per 12 s slot over 4 workers, are the load Glamsterdam is meant to make possible, not a scheduled value. The fork (EIP-7773) keeps 12 s slots, as EIP-7782's 6 s slots are not in it, and schedules the access lists (EIP-7928) but no gas limit; the advisory schedule (EIP-8261) raises mainnet's 60M gradually from the fork, its examples 75M then 90M, toward a higher value it does not name, and 200M is the figure reported for Sepolia. `--gas-per-slot 60000000` gives today's load.

It is its own Cargo workspace, so reth stays out of leanVM's. reth removed `reth_stateless` after v1.10.2, so it builds against that tag, with reth's own lockfile of that release.

## Fixtures

`fixtures/` holds 16 mainnet blocks (5991 transactions, 521M gas): 26444236 to 26444243, consecutive, and 26444286 to 26444636, every 50th, over the 80 minutes after. Each is the block and its execution witness as a reth node serves it (`debug_executionWitness`, here from the free endpoints of `https://rpc.nodeflare.app/eth/public`, `https://one.valve.city/rpc/vk_demo/evm/1` and `https://rpc-eth.blockmachine.io`). `el-load` rebuilds each block and checks it against mainnet's hash. A geth node's witness serves too (`el-load` takes its headers as JSON), but lacks for some blocks a trie node reth's state root needs, so those blocks do not validate; a reth node's is complete for reth. Public reth endpoints serve the witnesses of recent blocks only, and few a day for free: `fetch-fixtures.py` fetches others, trying its RPCs in turn:

```bash
bench/el-load/fetch-fixtures.py https://rpc.nodeflare.app/eth/public,https://rpc-eth.blockmachine.io bench/el-load/fixtures 26444236
```

## What it leaves out

A node reads the state a block touches from its database and writes the result back; stateless validation reads it from the witness instead, and keeps the result in memory.
