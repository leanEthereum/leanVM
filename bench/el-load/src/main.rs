//! An execution client's load, next to the prover: validates mainnet blocks as a stateless reth node does
//! (`reth_stateless`), a slot's worth of gas per slot, spread over parallel workers as block-level access lists let a
//! client spread one block. Validating a block verifies its transactions' signatures, verifies the witness (the Merkle
//! proofs of everything it touches) against the parent's state root, executes it, checks its receipts and gas, and
//! recomputes the state root, which must be the block's. The blocks and their witnesses are `fixtures/`, from
//! `fetch-fixtures.py`.
//!
//! - `el-load check FIXTURES`: validates each block once.
//! - `el-load run FIXTURES [--gas-per-slot G] [--slot-ms MS] [--workers W] [--slots N] [--db FILE [--db-gib G]
//!   [--db-miss M]]`: one line per slot, its gas and wall time, until killed or after N slots. `--slot-ms 0` runs the
//!   slots back to back. With `--db`, each block also does a node's database I/O (`db.rs`) on FILE, of G GiB (16), its
//!   cache missing an M share (1) of the accounts and slots the block touches.

mod db;

use alloy_consensus::{BlockHeader, Header};
use alloy_primitives::{Bytes, keccak256};
use reth_chainspec::MAINNET;
use reth_ethereum_primitives::Block;
use reth_evm_ethereum::EthEvmConfig;
use reth_stateless::{ExecutionWitness, UncompressedPublicKey, stateless_validation};
use serde_json::Value;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

struct Fixture {
    block: Block,
    public_keys: Vec<UncompressedPublicKey>,
    witness: ExecutionWitness,
}

impl Fixture {
    fn gas(&self) -> u64 {
        self.block.header.gas_used()
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let value = |name: &str| args.iter().position(|a| a == name).map(|i| args[i + 1].as_str());
    let flag = |name: &str, default: u64| value(name).map_or(default, |v| v.parse().expect("a number"));
    let (Some(command), Some(dir)) = (args.first(), args.get(1)) else {
        panic!("usage: el-load check|run FIXTURES [--gas-per-slot G] [--slot-ms MS] [--workers W] [--slots N] [--db FILE]")
    };
    let db = value("--db").map(|path| {
        let miss = value("--db-miss").map_or(1.0, |v| v.parse().expect("a share"));
        db::Db::open(path, flag("--db-gib", 16), miss)
    });
    let fixtures = load(dir);
    match command.as_str() {
        "check" => check(&fixtures),
        "run" => run(
            &fixtures,
            flag("--gas-per-slot", 200_000_000),
            flag("--slot-ms", 12_000),
            flag("--workers", 4) as usize,
            flag("--slots", 0),
            db.as_ref(),
        ),
        _ => panic!("unknown command {command}"),
    }
}

/// Validates a block, returning how many accounts and slots it changes.
fn validate(f: &Fixture) -> usize {
    try_validate(f).unwrap_or_else(|e| panic!("{e}"))
}

fn try_validate(f: &Fixture) -> Result<usize, String> {
    stateless_validation(
        f.block.clone(),
        f.public_keys.clone(),
        f.witness.clone(),
        MAINNET.clone(),
        EthEvmConfig::mainnet(),
    )
    .map(|(_, output)| output.state.state.values().map(|account| 1 + account.storage.len()).sum())
    .map_err(|e| format!("block {} does not validate: {e}", f.block.header.number))
}

fn check(fixtures: &[Fixture]) {
    let mut valid = true;
    for f in fixtures {
        let start = Instant::now();
        match try_validate(f) {
            Ok(_) => println!(
                "block {}: {} transactions, {} gas, valid, {:.1} ms",
                f.block.header.number,
                f.block.body.transactions.len(),
                f.gas(),
                start.elapsed().as_secs_f64() * 1e3
            ),
            Err(e) => {
                println!("{e}");
                valid = false;
            }
        }
    }
    assert!(valid, "some blocks do not validate");
}

fn run(fixtures: &[Fixture], gas_per_slot: u64, slot_ms: u64, workers: usize, slots: u64, db: Option<&db::Db>) {
    // One-time setup out of the timings, such as the KZG trusted setup a blob proof loads.
    for f in fixtures {
        validate(f);
    }
    let mut next = 0;
    for slot in 1.. {
        let start = Instant::now();
        // Whole blocks, in turn, until the slot's gas is reached.
        let mut todo = Vec::new();
        let mut gas = 0;
        while gas < gas_per_slot {
            let f = &fixtures[next % fixtures.len()];
            todo.push(f);
            gas += f.gas();
            next += 1;
        }
        let taken = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..workers {
                s.spawn(|| {
                    while let Some(f) = todo.get(taken.fetch_add(1, Ordering::Relaxed)) {
                        let changed = validate(f);
                        if let Some(db) = db {
                            db.block(f.witness.keys.len(), changed);
                        }
                    }
                });
            }
        });
        let elapsed = start.elapsed();
        println!("slot {slot}: {gas} gas in {:.1} ms", elapsed.as_secs_f64() * 1e3);
        if slot == slots {
            break;
        }
        if let Some(rest) = Duration::from_millis(slot_ms).checked_sub(elapsed) {
            std::thread::sleep(rest);
        }
    }
}

fn load(dir: &str) -> Vec<Fixture> {
    let mut paths: Vec<_> = std::fs::read_dir(dir).expect("the fixtures").map(|e| e.unwrap().path()).collect();
    paths.sort();
    paths
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .map(|p| fixture(serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap()))
        .collect()
}

/// A fixture: the block rebuilt from the RPC's JSON, checked against mainnet's hash, its senders' keys, and its witness.
fn fixture(mut json: Value) -> Fixture {
    let rpc: alloy_rpc_types_eth::Block = serde_json::from_value(json["block"].take()).unwrap();
    let hash = rpc.header.hash;
    let block: Block = rpc.into_consensus().map_transactions(Into::into);
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

    // As a reth node serves it, or a geth one: headers as JSON there, which reth takes as RLP, and no keys.
    let w = &json["witness"];
    let hex = |v: &Value| v.as_array().map_or(Vec::new(), |a| a.iter().map(|v| v.as_str().unwrap().parse().unwrap()).collect());
    let headers = w["headers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| match h.as_str() {
            Some(rlp) => rlp.parse().unwrap(),
            None => {
                let rpc: alloy_rpc_types_eth::Header = serde_json::from_value(h.clone()).unwrap();
                let rlp = Bytes::from(alloy_rlp::encode(&rpc.inner as &Header));
                assert_eq!(keccak256(&rlp), rpc.hash, "header {} rebuilt with another hash", rpc.inner.number);
                rlp
            }
        })
        .collect();
    let witness = ExecutionWitness { state: hex(&w["state"]), codes: hex(&w["codes"]), keys: hex(&w["keys"]), headers };
    Fixture { block, public_keys, witness }
}
