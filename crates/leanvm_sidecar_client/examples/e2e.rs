//! The run `bins/leanvm-sidecar/e2e.sh` drives:
//! e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>
//!
//! Sixteen `AGGREGATE` requests of `signatures-per-batch` signatures each, one after the other, then
//! one `RECURSE` over the sixteen proofs and one `VERIFY` of the result. With `sub-batch` below
//! `signatures-per-batch`, each batch is instead built up in parts of `sub-batch` signatures: an
//! `AGGREGATE`, then one `EXTEND` per part of the proof so far, which the server keeps. Parts run at
//! rate 1, except the last at `aggregate-rate`. The file is records of `pubkey | message | signature`.

use leanvm_sidecar_client::{
    Client, FLAG_KEEP_PROOF, FLAG_USE_KEPT, OP_AGGREGATE, OP_EXTEND, OP_RECURSE, OP_VERIFY, Response, ST_OK,
};
use std::time::{Duration, Instant};

const BATCHES: usize = 16;
const RESP_CAP: usize = 16 << 20;

/// Send one request and wait for its response.
fn call(client: &mut Client, op: u32, flags: u32, rate: u32, payload: &[u8]) -> (Response, Duration) {
    let started = Instant::now();
    let id = client.send(op, flags, rate, payload, RESP_CAP).expect("no room in the channel");
    let response = loop {
        match client.try_recv() {
            Some(response) => break response,
            None => std::thread::sleep(Duration::from_micros(100)),
        }
    };
    assert_eq!(response.id, id);
    (response, started.elapsed())
}

fn check(response: &Response) {
    if response.status != ST_OK {
        let text = String::from_utf8_lossy(&response.body);
        println!("  FAILED: status {} detail {}: {text}", response.status, response.detail);
        std::process::exit(1);
    }
}

/// A `proof | claims` body as `(proof, claims)`, each with its length prefix.
fn split(response: &Response) -> (&[u8], &[u8]) {
    check(response);
    let proof_len = u64::from_le_bytes(response.body[..8].try_into().unwrap()) as usize;
    response.body.split_at(8 + proof_len)
}

fn claim_count(claims: &[u8]) -> u32 {
    u32::from_le_bytes(claims[..4].try_into().unwrap())
}

/// One proving request: prints the step as `what`, with the time since `since` if given, and returns
/// the response's `(proof, claims)`.
fn step(
    client: &mut Client,
    op: u32,
    flags: u32,
    rate: u32,
    payload: &[u8],
    what: &str,
    since: Option<Instant>,
) -> (Vec<u8>, Vec<u8>) {
    let (response, elapsed) = call(client, op, flags, rate, payload);
    let batch = since.map(|since| format!(", batch total {:.3} s", since.elapsed().as_secs_f64())).unwrap_or_default();
    let (proof, claims) = split(&response);
    println!(
        "{what}, {} bytes, rate {rate} -> proof {} bytes, {} claims, {:.3} s{batch}",
        payload.len(),
        proof.len() - 8,
        claim_count(claims),
        elapsed.as_secs_f64(),
    );
    (proof.to_vec(), claims.to_vec())
}

/// `AGGREGATE` over `records`, each `record` bytes; under `FLAG_USE_KEPT`, `EXTEND` of the proof the
/// server kept with them.
fn aggregate(
    client: &mut Client,
    flags: u32,
    records: &[u8],
    record: usize,
    rate: u32,
    label: &str,
    since: Option<Instant>,
) -> (Vec<u8>, Vec<u8>) {
    let count = records.len() / record;
    let mut payload = Vec::new();
    let (op, what) = if flags & FLAG_USE_KEPT != 0 {
        // No child in the payload.
        payload.extend(0u32.to_le_bytes());
        (OP_EXTEND, format!("{label}: kept proof + {count} signatures"))
    } else {
        (OP_AGGREGATE, format!("{label}: {count} signatures"))
    };
    payload.extend((count as u32).to_le_bytes());
    payload.extend(records);
    step(client, op, flags, rate, &payload, &what, since)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let [_, channel, signatures, aggregate_rate, recurse_rate, per_batch, sub_batch] = args.as_slice() else {
        eprintln!(
            "usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate> <signatures-per-batch> <sub-batch>"
        );
        std::process::exit(2);
    };
    let aggregate_rate: u32 = aggregate_rate.parse().expect("aggregate rate");
    let recurse_rate: u32 = recurse_rate.parse().expect("recurse rate");
    let per_batch: usize = per_batch.parse().expect("signatures per batch");
    let sub_batch: usize = sub_batch.parse().expect("sub-batch");
    let mut client = Client::open(channel.as_ref()).expect("open channel");
    let record = client.pub_key_size() + client.message_len() + client.sig_size();
    let signatures = std::fs::read(signatures).expect("read signatures");
    assert!(signatures.len() >= BATCHES * per_batch * record, "signature file too short");

    let total = Instant::now();
    let parts = per_batch.div_ceil(sub_batch);
    let mut recurse = (BATCHES as u32).to_le_bytes().to_vec();
    for (batch, records) in signatures.chunks_exact(per_batch * record).take(BATCHES).enumerate() {
        let mut proved = (Vec::new(), Vec::new());
        let started = Instant::now();
        for (part, records) in records.chunks(sub_batch * record).enumerate() {
            let (first, last) = (part == 0, part + 1 == parts);
            let name = if first { "aggregate" } else { "extend   " };
            let mut label = format!("{name} {:2}/{BATCHES}", batch + 1);
            if parts > 1 {
                label += &format!(" part {:2}/{parts}", part + 1);
            }
            // Every part but the first extends the proof the server kept; every part but the last
            // has it keep the new one. The last part's proof is the batch's.
            let flags = if first { 0 } else { FLAG_USE_KEPT } | if last { 0 } else { FLAG_KEEP_PROOF };
            let rate = if last { aggregate_rate } else { 1 };
            let since = (parts > 1 && last).then_some(started);
            proved = aggregate(&mut client, flags, records, record, rate, &label, since);
        }
        let (proof, claims) = proved;
        recurse.extend(claims);
        recurse.extend(proof);
    }
    let what = format!("recurse {BATCHES} -> 1: {BATCHES} proofs");
    let (proof, claims) = step(&mut client, OP_RECURSE, 0, recurse_rate, &recurse, &what, None);
    let verify = [claims.as_slice(), &proof].concat();
    let (verdict, elapsed) = call(&mut client, OP_VERIFY, 0, 0, &verify);
    check(&verdict);
    println!(
        "verify: proof {} bytes, {} claims, {} bytes -> valid, {:.3} s",
        proof.len() - 8,
        claim_count(&claims),
        verify.len(),
        elapsed.as_secs_f64(),
    );
    println!("total: {:.3} s", total.elapsed().as_secs_f64());
}
