//! The run `bins/leanvm-sidecar/e2e.sh` drives: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>
//!
//! Sixteen `AGGREGATE` requests of 1500 signatures each, one after the other, then one `RECURSE`
//! over the sixteen proofs. The file is records of `pubkey | message | signature`.

use leanvm_sidecar_client::{Client, OP_AGGREGATE, OP_RECURSE, Response, ST_OK};
use std::time::{Duration, Instant};

const BATCHES: usize = 16;
const PER_BATCH: usize = 1500;
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

/// A `proof | claims` body as `(proof, claims)`, each with its length prefix.
fn split(response: &Response) -> (&[u8], &[u8]) {
    if response.status != ST_OK {
        let text = String::from_utf8_lossy(&response.body);
        println!("  FAILED: status {} detail {}: {text}", response.status, response.detail);
        std::process::exit(1);
    }
    let proof_len = u64::from_le_bytes(response.body[..8].try_into().unwrap()) as usize;
    response.body.split_at(8 + proof_len)
}

fn claim_count(claims: &[u8]) -> u32 {
    u32::from_le_bytes(claims[..4].try_into().unwrap())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let [_, channel, signatures, aggregate_rate, recurse_rate] = args.as_slice() else {
        eprintln!("usage: e2e <channel> <signatures-file> <aggregate-rate> <recurse-rate>");
        std::process::exit(2);
    };
    let aggregate_rate: u32 = aggregate_rate.parse().expect("aggregate rate");
    let recurse_rate: u32 = recurse_rate.parse().expect("recurse rate");
    let mut client = Client::open(channel.as_ref()).expect("open channel");
    let record = client.pub_key_size() + client.message_len() + client.sig_size();
    let signatures = std::fs::read(signatures).expect("read signatures");
    assert!(signatures.len() >= BATCHES * PER_BATCH * record, "signature file too short");

    let total = Instant::now();
    let mut recurse = (BATCHES as u32).to_le_bytes().to_vec();
    for (batch, records) in signatures.chunks_exact(PER_BATCH * record).take(BATCHES).enumerate() {
        let mut payload = (PER_BATCH as u32).to_le_bytes().to_vec();
        payload.extend(records);
        let (response, elapsed) = call(&mut client, OP_AGGREGATE, 0, aggregate_rate, &payload);
        let (proof, claims) = split(&response);
        println!(
            "aggregate {:2}/{BATCHES}: {PER_BATCH} signatures, {} bytes, rate {aggregate_rate} -> \
             proof {} bytes, {} claims, {:.3} s",
            batch + 1,
            payload.len(),
            proof.len() - 8,
            claim_count(claims),
            elapsed.as_secs_f64(),
        );
        recurse.extend(claims);
        recurse.extend(proof);
    }
    let (response, elapsed) = call(&mut client, OP_RECURSE, 0, recurse_rate, &recurse);
    let (proof, claims) = split(&response);
    println!(
        "recurse {BATCHES} -> 1: {BATCHES} proofs, {} bytes, rate {recurse_rate} -> proof {} bytes, {} claims, {:.3} s",
        recurse.len(),
        proof.len() - 8,
        claim_count(claims),
        elapsed.as_secs_f64(),
    );
    println!("total: {:.3} s", total.elapsed().as_secs_f64());
}
