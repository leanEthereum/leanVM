//! An execution client's load: validates mainnet blocks as a stateless reth node does, with a node's database I/O
//! (`db.rs`), one worker per CPU it may use, each starting the next block as soon as it is done.
//!
//! Usage: `el-load FIXTURES DB`. It first validates each block once, then prints after each block the total so far.

mod db;

use reth_chainspec::MAINNET;
use reth_ethereum_primitives::Block;
use reth_evm_ethereum::EthEvmConfig;
use reth_stateless::{ExecutionWitness, UncompressedPublicKey, stateless_validation};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

struct Fixture {
    block: Block,
    public_keys: Vec<UncompressedPublicKey>,
    witness: ExecutionWitness,
}

#[derive(serde::Deserialize)]
struct Json {
    block: alloy_rpc_types_eth::Block,
    witness: ExecutionWitness,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [fixtures, db] = &args[..] else { panic!("usage: el-load FIXTURES DB") };
    let db = db::Db::open(db);
    let fixtures = load(fixtures);
    for f in &fixtures {
        let start = Instant::now();
        validate(f);
        let ms = start.elapsed().as_secs_f64() * 1e3;
        println!("block {}: {} gas, valid, {ms:.1} ms", f.block.header.number, f.block.header.gas_used);
    }

    let start = Instant::now();
    let (next, gas) = (AtomicU64::new(0), AtomicU64::new(0));
    std::thread::scope(|s| {
        for _ in 0..std::thread::available_parallelism().unwrap().get() {
            s.spawn(|| {
                loop {
                    let f = &fixtures[next.fetch_add(1, Ordering::Relaxed) as usize % fixtures.len()];
                    db.block(f.witness.keys.len(), validate(f));
                    let gas = gas.fetch_add(f.block.header.gas_used, Ordering::Relaxed) + f.block.header.gas_used;
                    let s = start.elapsed().as_secs_f64();
                    println!("{} Mgas in {s:.1} s: {:.0} Mgas/s", gas / 1_000_000, gas as f64 / s / 1e6);
                }
            });
        }
    });
}

/// Validates a block, returning how many accounts and slots it changes.
fn validate(f: &Fixture) -> usize {
    let (_, output) = stateless_validation(
        f.block.clone(),
        f.public_keys.clone(),
        f.witness.clone(),
        MAINNET.clone(),
        EthEvmConfig::mainnet(),
    )
    .unwrap_or_else(|e| panic!("block {} does not validate: {e}", f.block.header.number));
    output.state.state.values().map(|account| 1 + account.storage.len()).sum()
}

/// The fixtures: each block rebuilt from the RPC's JSON and checked against mainnet's hash, its senders' keys, and its
/// witness.
fn load(dir: &str) -> Vec<Fixture> {
    let mut paths: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    paths.sort();
    paths
        .iter()
        .map(|p| {
            let json: Json = serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap();
            let hash = json.block.header.hash;
            let block: Block = json.block.into_consensus().map_transactions(Into::into);
            assert_eq!(block.header.hash_slow(), hash, "block {} rebuilt with another hash", block.header.number);
            let public_keys = block
                .body
                .transactions
                .iter()
                .map(|tx| {
                    let key = tx.signature().recover_from_prehash(&tx.signature_hash()).unwrap();
                    UncompressedPublicKey(key.to_encoded_point(false).as_bytes().try_into().unwrap())
                })
                .collect();
            Fixture { block, public_keys, witness: json.witness }
        })
        .collect()
}
