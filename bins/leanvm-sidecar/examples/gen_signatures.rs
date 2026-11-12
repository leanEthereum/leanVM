//! Write the valid leanXMSS signatures `e2e.sh` reads: gen_signatures <count> <file>
//!
//! The file is `count` records of `pubkey | message | signature`, the triple of an `AGGREGATE`
//! payload. Every record has its own signer; signer `i` signs message `i mod MESSAGES`, whose
//! bytes all equal that number. Signers are mock keys, real at the one leaf index they sign at,
//! so their signatures verify like a full key's; the secret keys are derived from the record index
//! and worth nothing.

use signatures::lean_xmss::{LeafIndex, MESSAGE_LEN, PUB_KEY_SIZE, SIG_SIZE, mock};
use std::io::Write;

const MESSAGES: usize = 4;
const LEAF_INDEX: LeafIndex = 0;
const RECORD: usize = PUB_KEY_SIZE + MESSAGE_LEN + SIG_SIZE;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (count, path) = match args.as_slice() {
        [_, count, path] => (count.parse::<usize>().expect("count"), path),
        _ => {
            eprintln!("usage: gen_signatures <count> <file>");
            std::process::exit(2);
        }
    };
    let mut records = vec![0u8; count * RECORD];
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let per_worker = count.div_ceil(workers).max(1);
    std::thread::scope(|scope| {
        for (worker, chunk) in records.chunks_mut(per_worker * RECORD).enumerate() {
            scope.spawn(move || {
                for (offset, record) in chunk.as_chunks_mut::<RECORD>().0.iter_mut().enumerate() {
                    let index = worker * per_worker + offset;
                    // One seed per signer, always over the one leaf: a seed backs one key only (`mock`).
                    let mut seed = [0x5e; 32];
                    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
                    let (secret_key, pub_key) = mock::key_gen_from_seed(seed, LEAF_INDEX, LEAF_INDEX);
                    let message = [(index % MESSAGES) as u8; MESSAGE_LEN];
                    let signature = mock::sign(&secret_key, &message, LEAF_INDEX).unwrap();
                    let (head, tail) = record.split_at_mut(PUB_KEY_SIZE + MESSAGE_LEN);
                    head[..PUB_KEY_SIZE].copy_from_slice(&pub_key.to_bytes());
                    head[PUB_KEY_SIZE..].copy_from_slice(&message);
                    tail.copy_from_slice(&signature.to_bytes());
                }
            });
        }
    });
    std::fs::File::create(path).and_then(|mut file| file.write_all(&records)).expect("write");
}
