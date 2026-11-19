# el-load

An execution client's load, for `bench/bench-alongside-el.sh`: it validates mainnet blocks as a stateless [reth](https://github.com/paradigmxyz/reth) node does (`reth_stateless::stateless_validation`: signatures, the witness's Merkle proofs, execution, receipts, the state root), with a node's database I/O on a 16 GiB file (`src/db.rs`), one worker per CPU it may use, without pause. It is its own Cargo workspace, on reth v1.10.2 (reth's last release with `reth_stateless`) and that release's lockfile.

`fixtures/` holds 16 mainnet blocks (26444236 to 26444243, and every 50th block from 26444286 to 26444636), each with its execution witness from a reth node, fetched with `fetch-fixtures.py RPC_URL bench/el-load/fixtures BLOCK...` from an RPC serving `debug_executionWitness`, such as `https://rpc.nodeflare.app/eth/public`.
