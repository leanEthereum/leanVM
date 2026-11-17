//! Write the valid leanXMSS signatures `e2e.sh` reads: gen_signatures <count> <file>
//!
//! The file is `count` records of `pubkey | message | signature`, the triple of an `AGGREGATE`
//! payload. A full key is slow to generate, so the records share `KEYS` keys: record `i` is key
//! `i mod KEYS` signing, at leaf index `i / KEYS`, the message whose bytes spell that index. No two
//! records make the same claim, and no key signs twice at one leaf. The secret keys are derived
//! from the key's number and worth nothing.

use lean_vm::lean_xmss::{self, LeafIndex, MESSAGE_LEN, PUB_KEY_SIZE, SECRET_KEY_LEN, SIG_SIZE};
use std::io::Write;

const KEYS: usize = 32;
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
    // One thread per key: its records are every `KEYS`-th, from its own number.
    let per_key: Vec<Vec<[u8; RECORD]>> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..KEYS.min(count))
            .map(|key| {
                scope.spawn(move || {
                    let mut seed = [0x5e; SECRET_KEY_LEN];
                    seed[..8].copy_from_slice(&(key as u64).to_le_bytes());
                    let (secret_key, pub_key) = lean_xmss::key_gen(&seed);
                    let record = |index: usize| {
                        let leaf_index = (index / KEYS) as LeafIndex;
                        let mut message = [0u8; MESSAGE_LEN];
                        message[..4].copy_from_slice(&leaf_index.to_le_bytes());
                        let signature = lean_xmss::sign(&secret_key, &message, leaf_index);
                        let mut record = [0u8; RECORD];
                        let (head, tail) = record.split_at_mut(PUB_KEY_SIZE + MESSAGE_LEN);
                        head[..PUB_KEY_SIZE].copy_from_slice(&pub_key.to_bytes());
                        head[PUB_KEY_SIZE..].copy_from_slice(&message);
                        tail.copy_from_slice(&signature.to_bytes());
                        record
                    };
                    (key..count).step_by(KEYS).map(record).collect()
                })
            })
            .collect();
        workers.into_iter().map(|worker| worker.join().unwrap()).collect()
    });
    let mut file = std::io::BufWriter::new(std::fs::File::create(path).expect("create"));
    for index in 0..count {
        file.write_all(&per_key[index % KEYS][index / KEYS]).expect("write");
    }
    file.flush().expect("write");
}
