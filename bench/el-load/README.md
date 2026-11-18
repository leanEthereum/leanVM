# el-load

An execution client's load, to run next to the prover (`bench/bench-alongside-el.sh`). It re-executes real mainnet blocks with [revm](https://github.com/bluealloy/revm), a slot's worth of gas per slot, spread over parallel workers the way block-level access lists (EIP-7928, Glamsterdam) let a client spread one block's transactions.

```bash
cargo build --release --manifest-path bench/el-load/Cargo.toml
bench/el-load/target/release/el-load check bench/el-load/fixtures
bench/el-load/target/release/el-load run bench/el-load/fixtures --gas-per-slot 200000000 --slot-ms 12000 --workers 4
```

- `check` executes each block once and checks that every transaction uses exactly the gas mainnet's receipt records.
- `run` prints each slot's gas and wall time, until killed or after `--slots N`. The defaults, 200M gas per 12 s slot over 4 workers, are the load Glamsterdam is meant to make possible, not a scheduled value. The fork (EIP-7773) keeps 12 s slots, as EIP-7782's 6 s slots are not in it, and schedules the access lists (EIP-7928) but no gas limit; the advisory schedule (EIP-8261) raises mainnet's 60M gradually from the fork, its examples 75M then 90M, toward a higher value it does not name, and 200M is the figure reported for Sepolia. `--gas-per-slot 60000000` gives today's load, and `--slot-ms 0` runs the slots back to back.

It is its own Cargo workspace, so revm stays out of leanVM's.

## Fixtures

`fixtures/` holds 16 mainnet blocks (4526 transactions, 427M gas): 26443442 to 26443449, consecutive, and 26436576 to 26442876, every 900th, spread over the day before. Each comes with its transactions, its pre-state (every account, storage slot and code its transactions touch, EIP-7702 delegation targets included), the 256 block hashes `BLOCKHASH` can read, and each transaction's gas used. `fetch-fixtures.py` produced them from `https://eth.drpc.org`, and regenerates them, or fetches others, from any RPC that serves `debug_traceBlockByNumber` with `prestateTracer`:

```bash
bench/el-load/fetch-fixtures.py https://eth.drpc.org bench/el-load/fixtures 26443442 26443443
```

## What it leaves out

It replays with revm from the recorded pre-state, not with reth's stateless validation (`reth_stateless`), which needs each block's execution witness: no public RPC tried serves `debug_executionWitness`, and building one from `eth_getProof` needs historical state the public RPCs do not keep ("Unknown state" a few hundred blocks back), so a witness needs a synced node of one's own.

It runs the EVM only. A node also recovers each transaction's sender, reads its state from a database and recomputes the state root, so this load is a lower bound on a client's. The blocks run under Osaka's rules, from their pre-state alone: the beacon-root and block-hash system calls before the transactions and the withdrawals after them are not applied, which no transaction in these blocks depends on (`check` would show it).
