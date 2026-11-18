# el-load

An execution client's load, to run next to the prover (`bench/bench-alongside-el.sh`). It re-executes real mainnet blocks with [revm](https://github.com/bluealloy/revm), a slot's worth of gas per slot, spread over parallel workers the way block-level access lists (EIP-7928, Glamsterdam) let a client spread one block's transactions.

```bash
cargo build --release --manifest-path bench/el-load/Cargo.toml
bench/el-load/target/release/el-load check bench/el-load/fixtures
bench/el-load/target/release/el-load run bench/el-load/fixtures --gas-per-slot 200000000 --slot-ms 12000 --workers 4
```

- `check` executes each block once and checks that every transaction uses exactly the gas mainnet's receipt records.
- `run` prints each slot's gas and wall time, until killed or after `--slots N`. The defaults, 200M gas per 12 s slot over 4 workers, are the load Glamsterdam is meant to make possible: the fork keeps 12 s slots (EIP-7782's 6 s slots were declined) and raises no gas limit itself (EIP-7773), but its access lists are what let validators raise mainnet's, 60M at the fork, toward the 200M Sepolia runs at. `--gas-per-slot 60000000` gives today's load, and `--slot-ms 0` runs the slots back to back.

It is its own Cargo workspace, so revm stays out of leanVM's.

## Fixtures

`fixtures/` holds mainnet blocks 26443442 to 26443449 (8 consecutive blocks, 2510 transactions, 221M gas), each with its transactions, its pre-state (every account, storage slot and code its transactions touch, EIP-7702 delegation targets included), the 256 block hashes `BLOCKHASH` can read, and each transaction's gas used. `fetch-fixtures.py` produced them from `https://eth.drpc.org`, and regenerates them, or fetches others, from any RPC that serves `debug_traceBlockByNumber` with `prestateTracer`:

```bash
bench/el-load/fetch-fixtures.py https://eth.drpc.org bench/el-load/fixtures 26443442 26443443
```

## What it leaves out

It runs the EVM only. A node also recovers each transaction's sender, reads its state from a database and recomputes the state root, so this load is a lower bound on a client's. The blocks run under Osaka's rules, from their pre-state alone: the beacon-root and block-hash system calls before the transactions and the withdrawals after them are not applied, which no transaction in these blocks depends on (`check` would show it).
