//! An execution client's load, next to the prover: re-executes mainnet blocks with revm from their recorded pre-state
//! (`fixtures/`, from `fetch-fixtures.py`), a slot's worth of gas per slot, spread over parallel workers as block-level
//! access lists let a client spread one block.
//!
//! - `el-load check FIXTURES`: executes each block once and checks every transaction's gas against mainnet's receipts.
//! - `el-load run FIXTURES [--gas-per-slot G] [--slot-ms MS] [--workers W] [--slots N]`: one line per slot, its gas and
//!   wall time, until killed or after N slots. `--slot-ms 0` runs the slots back to back.

use revm::context::either::Either;
use revm::context::transaction::{AccessList, AccessListItem, Authorization, SignedAuthorization};
use revm::context::{BlockEnv, TxEnv};
use revm::database::{CacheDB, EmptyDB};
use revm::primitives::hardfork::SpecId;
use revm::primitives::{Address, Bytes, TxKind, U256};
use revm::state::{AccountInfo, Bytecode};
use revm::{Context, ExecuteCommitEvm, MainBuilder, MainContext};
use serde_json::Value;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// Mainnet's blob base fee update fraction since its second blob-parameter-only fork.
const BLOB_BASE_FEE_UPDATE_FRACTION: u64 = 11_684_671;

struct Fixture {
    number: u64,
    block: BlockEnv,
    txs: Vec<TxEnv>,
    gas_used: Vec<u64>,
    gas: u64,
    prestate: CacheDB<EmptyDB>,
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str, default: u64| {
        args.iter()
            .position(|a| a == name)
            .map_or(default, |i| args[i + 1].parse().expect("a number"))
    };
    let (Some(command), Some(dir)) = (args.first(), args.get(1)) else {
        panic!("usage: el-load check|run FIXTURES [--gas-per-slot G] [--slot-ms MS] [--workers W] [--slots N]")
    };
    let fixtures = load(dir);
    // One-time setup, such as the KZG trusted setup a blob proof loads, kept out of the timings.
    fixtures.iter().for_each(|f| drop(execute(f)));
    match command.as_str() {
        "check" => check(&fixtures),
        "run" => run(
            &fixtures,
            flag("--gas-per-slot", 200_000_000),
            flag("--slot-ms", 12_000),
            flag("--workers", 4) as usize,
            flag("--slots", 0),
        ),
        _ => panic!("unknown command {command}"),
    }
}

/// Executes a block on its pre-state, returning each transaction's gas used.
fn execute(f: &Fixture) -> Vec<u64> {
    let mut evm = Context::mainnet()
        .with_db(CacheDB::new(&f.prestate))
        .with_block(f.block.clone())
        .modify_cfg_chained(|cfg| {
            cfg.spec = SpecId::OSAKA;
            cfg.chain_id = 1;
            cfg.blob_base_fee_update_fraction = Some(BLOB_BASE_FEE_UPDATE_FRACTION);
        })
        .build_mainnet();
    f.txs.iter().map(|tx| evm.transact_commit(tx.clone()).map_or(0, |r| r.tx_gas_used())).collect()
}

fn check(fixtures: &[Fixture]) {
    let mut ok = true;
    for f in fixtures {
        let start = Instant::now();
        let gas = execute(f);
        let elapsed = start.elapsed();
        let wrong = gas.iter().zip(&f.gas_used).filter(|(a, b)| a != b).count();
        ok &= wrong == 0;
        println!(
            "block {}: {} transactions, {} gas, {wrong} with other gas than mainnet, {:.1} ms",
            f.number,
            f.txs.len(),
            f.gas,
            elapsed.as_secs_f64() * 1e3
        );
    }
    assert!(ok, "the replay differs from mainnet");
}

fn run(fixtures: &[Fixture], gas_per_slot: u64, slot_ms: u64, workers: usize, slots: u64) {
    let mut next = 0;
    for slot in 1.. {
        let start = Instant::now();
        // Whole blocks, in turn, until the slot's gas is reached.
        let mut todo = Vec::new();
        let mut gas = 0;
        while gas < gas_per_slot {
            todo.push(&fixtures[next % fixtures.len()]);
            gas += fixtures[next % fixtures.len()].gas;
            next += 1;
        }
        let taken = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..workers {
                s.spawn(|| {
                    while let Some(f) = todo.get(taken.fetch_add(1, Ordering::Relaxed)) {
                        execute(f);
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
        .map(|p| fixture(&serde_json::from_slice(&std::fs::read(p).unwrap()).unwrap()))
        .collect()
}

fn fixture(json: &Value) -> Fixture {
    let b = &json["block"];
    let mut block = BlockEnv {
        number: U256::from(int(&b["number"])),
        beneficiary: parse(&b["miner"]),
        timestamp: U256::from(int(&b["timestamp"])),
        gas_limit: int(&b["gasLimit"]),
        basefee: int(&b["baseFeePerGas"]),
        difficulty: parse(&b["difficulty"]),
        prevrandao: Some(parse(&b["mixHash"])),
        ..Default::default()
    };
    block.set_blob_excess_gas_and_price(int(&b["excessBlobGas"]), BLOB_BASE_FEE_UPDATE_FRACTION);

    let mut prestate = CacheDB::new(EmptyDB::default());
    for (address, account) in json["prestate"].as_object().unwrap() {
        let address: Address = address.parse().unwrap();
        let code = Bytecode::new_raw(account.get("code").map_or_else(Bytes::new, parse));
        let info = AccountInfo {
            balance: account.get("balance").map_or(U256::ZERO, parse),
            nonce: account.get("nonce").and_then(Value::as_u64).unwrap_or(0),
            code_hash: code.hash_slow(),
            code: Some(code),
            ..Default::default()
        };
        prestate.insert_account_info(address, info);
        for (slot, value) in account["storage"].as_object().unwrap() {
            prestate
                .insert_account_storage(address, parse(&Value::from(slot.as_str())), parse(value))
                .unwrap();
        }
    }
    for (number, hash) in json["block_hashes"].as_object().unwrap() {
        prestate.cache.block_hashes.insert(parse(&Value::from(number.as_str())), parse(hash));
    }

    Fixture {
        number: int(&b["number"]),
        gas: int(&b["gasUsed"]),
        txs: b["transactions"].as_array().unwrap().iter().map(tx).collect(),
        gas_used: json["gas_used"].as_array().unwrap().iter().map(int).collect(),
        block,
        prestate,
    }
}

fn tx(t: &Value) -> TxEnv {
    let typ = int(&t["type"]) as u8;
    let dynamic_fee = typ >= 2;
    TxEnv {
        tx_type: typ,
        caller: parse(&t["from"]),
        gas_limit: int(&t["gas"]),
        gas_price: parse::<U256>(if dynamic_fee { &t["maxFeePerGas"] } else { &t["gasPrice"] }).to(),
        gas_priority_fee: dynamic_fee.then(|| parse::<U256>(&t["maxPriorityFeePerGas"]).to()),
        kind: t["to"].as_str().map_or(TxKind::Create, |to| TxKind::Call(to.parse().unwrap())),
        value: parse(&t["value"]),
        data: parse(&t["input"]),
        nonce: int(&t["nonce"]),
        chain_id: t.get("chainId").map(int),
        access_list: AccessList(
            t.get("accessList")
                .and_then(Value::as_array)
                .map_or(&[][..], Vec::as_slice)
                .iter()
                .map(|item| AccessListItem {
                    address: parse(&item["address"]),
                    storage_keys: item["storageKeys"].as_array().unwrap().iter().map(parse).collect(),
                })
                .collect(),
        ),
        blob_hashes: t.get("blobVersionedHashes").map_or(Vec::new(), |h| h.as_array().unwrap().iter().map(parse).collect()),
        max_fee_per_blob_gas: t.get("maxFeePerBlobGas").map_or(0, |f| parse::<U256>(f).to()),
        authorization_list: t.get("authorizationList").map_or(Vec::new(), |list| {
            list.as_array()
                .unwrap()
                .iter()
                .map(|a| {
                    let inner = Authorization {
                        chain_id: parse(&a["chainId"]),
                        address: parse(&a["address"]),
                        nonce: int(&a["nonce"]),
                    };
                    Either::Left(SignedAuthorization::new_unchecked(
                        inner,
                        int(&a["yParity"]) as u8,
                        parse(&a["r"]),
                        parse(&a["s"]),
                    ))
                })
                .collect()
        }),
    }
}

fn int(v: &Value) -> u64 {
    u64::from_str_radix(v.as_str().unwrap().trim_start_matches("0x"), 16).unwrap()
}

fn parse<T: std::str::FromStr>(v: &Value) -> T
where
    T::Err: std::fmt::Debug,
{
    v.as_str().unwrap().parse().unwrap()
}
