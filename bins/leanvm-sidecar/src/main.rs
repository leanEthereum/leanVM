//! leanVM as a service over shared memory: leanXMSS aggregation, recursion and verification for one
//! client process, in any language. `PROTOCOL.md` specifies the channel file and the encodings.

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

use clap::Parser;
use shm::{Channel, Ring};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use wire::{Request, Response, ST_OK, ST_RESP_TOO_SMALL};

mod serve;
mod shm;
mod warm;
mod wire;

/// Wait between polls of an empty request ring. Far below the cost of any request.
const IDLE_POLL: Duration = Duration::from_micros(100);

#[derive(Parser)]
struct Args {
    /// The channel file, created if missing. Put it on tmpfs (/dev/shm).
    #[arg(long)]
    path: PathBuf,

    /// Prover performance-worker count (1 = sequential). Default: the pool's own, one per physical core.
    #[arg(long, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
    threads: Option<usize>,

    /// Arena size in MiB. One request's payload and response regions both have to fit.
    #[arg(long, default_value_t = 64, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
    arena_mib: usize,

    /// Slots in each ring; a power of two.
    #[arg(long, default_value_t = 64)]
    ring_cap: u32,

    /// Signatures in the discarded warm-up proofs run before serving; 0 skips them. Set it to the
    /// largest batch expected: a larger proof than any before it still pays first-touch page faults.
    #[arg(long, default_value_t = 1500)]
    warmup_signatures: usize,

    /// WHIR inverse-rate logarithms to warm up, comma separated: the rates requests will ask for.
    #[arg(
        long,
        value_delimiter = ',',
        default_value = "1,2",
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new()
            .range(leanvm::MIN_LOG_INV_RATE as u64..=leanvm::MAX_LOG_INV_RATE as u64)
    )]
    warmup_rates: Vec<usize>,

    /// Print a timing tree per request. Use RUST_LOG to adjust verbosity.
    #[arg(long)]
    tracing: bool,
}

/// Serve requests one at a time until `stop`: `aggregate` must not run twice at once in a process.
fn run(chan: &Channel, stop: &AtomicBool) {
    let mut kept = None;
    while !stop.load(Ordering::Relaxed) {
        let Some(msg) = chan.pop(Ring::Request) else {
            std::thread::sleep(IDLE_POLL);
            continue;
        };
        let request = Request::decode(&msg);
        let _span = tracing::info_span!("request", id = request.id, op = request.op).entered();

        // Without a response region there is nowhere to put even an error's text.
        let writable = chan.in_arena(request.resp_off, request.resp_cap);
        let result = match chan.read(request.req_off, request.req_len) {
            Some(payload) if writable => serve::handle(&request, &payload, &mut kept),
            _ => Err(serve::Failure::bad_request("region outside the arena")),
        };
        let (status, detail, resp_len, body) = match result {
            Ok(body) if body.len() as u64 > request.resp_cap => (ST_RESP_TOO_SMALL, 0, body.len() as u64, Vec::new()),
            Ok(body) => (ST_OK, 0, body.len() as u64, body),
            Err(failure) => {
                let mut text = failure.text.into_bytes();
                text.truncate(if writable { request.resp_cap as usize } else { 0 });
                (failure.status, failure.detail, text.len() as u64, text)
            }
        };
        chan.write(request.resp_off, &body);
        let response = Response {
            id: request.id,
            status,
            detail,
            resp_len,
        };
        chan.push(Ring::Response, &response.encode());
    }
}

fn main() {
    let args = Args::parse();
    if let Some(threads) = args.threads {
        // SAFETY: no other thread exists yet. The pool reads this once, in `setup`.
        unsafe { std::env::set_var("LEANVM_NUM_THREADS", threads.to_string()) };
    }
    if args.tracing {
        bench::init_tracing();
    }
    leanvm::setup();
    if args.warmup_signatures > 0 {
        eprintln!("warming up...");
        let started = std::time::Instant::now();
        let signers = args.threads.or(std::thread::available_parallelism().ok().map(usize::from)).unwrap_or(1);
        let _quiet = bench::suppress_tracing();
        warm::warm_up(args.warmup_signatures, &args.warmup_rates, signers);
        eprintln!("warmed up in {:.1} s", started.elapsed().as_secs_f64());
    }
    let chan = match Channel::create(&args.path, args.ring_cap, args.arena_mib << 20) {
        Ok(chan) => chan,
        Err(error) => {
            eprintln!("{}: {error}", args.path.display());
            std::process::exit(1);
        }
    };
    eprintln!("serving {}", args.path.display());
    run(&chan, &AtomicBool::new(false));
}


#[cfg(test)]
mod tests {
    use super::*;
    use leanvm::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature, Message};
    use leanvm_sidecar_client::Client;
    use wire::*;

    const RING_CAP: u32 = 4;
    const ARENA_LEN: usize = 32 << 20;
    const LOG_INV_RATE: u32 = 2;
    const RESP_CAP: usize = 4 << 20;

    struct StopOnDrop<'a>(&'a AtomicBool);

    impl Drop for StopOnDrop<'_> {
        fn drop(&mut self) {
            self.0.store(true, Ordering::Relaxed);
        }
    }

    fn recv(client: &mut Client) -> leanvm_sidecar_client::Response {
        loop {
            match client.try_recv() {
                Some(response) => return response,
                None => std::thread::sleep(Duration::from_millis(1)),
            }
        }
    }

    /// The response's status, detail and body.
    fn call(client: &mut Client, op: u32, flags: u32, payload: &[u8]) -> (u32, u32, Vec<u8>) {
        let id = client.send(op, flags, LOG_INV_RATE, payload, RESP_CAP).unwrap();
        let response = recv(client);
        assert_eq!(response.id, id);
        (response.status, response.detail, response.body)
    }

    /// A `proof | claims` body.
    fn proved(status: u32, body: &[u8]) -> (Vec<u8>, leanvm::EthereumClaims) {
        assert_eq!(status, ST_OK, "{}", String::from_utf8_lossy(body));
        let mut reader = Reader(body);
        let proof = reader.proof().unwrap().to_vec();
        let claims = reader.claims().unwrap();
        reader.end().unwrap();
        (proof, claims)
    }

    fn signatures(triples: &[(LeanXmssPublicKey, Message, LeanXmssSignature)]) -> Vec<u8> {
        let mut out = (triples.len() as u32).to_le_bytes().to_vec();
        for (pub_key, message, signature) in triples {
            out.extend(pub_key.to_bytes());
            out.extend(message);
            out.extend(signature.to_bytes());
        }
        out
    }

    fn proof_with_claims(proof: &[u8], claims: &leanvm::EthereumClaims) -> Vec<u8> {
        let mut out = Vec::new();
        put_claims(&mut out, claims);
        put_proof(&mut out, proof);
        out
    }

    fn client(path: &std::path::Path) {
        let mut client = Client::open(path).unwrap();
        assert_eq!(client.sig_size(), lean_xmss::SIG_SIZE);

        let message = [7; lean_xmss::MESSAGE_LEN];
        let triples: Vec<_> = (0..3)
            .map(|leaf_index| {
                let (secret_key, pub_key) = lean_xmss::key_gen();
                (pub_key, message, lean_xmss::sign(&secret_key, &message, leaf_index).unwrap())
            })
            .collect();

        // Two requests in flight: answered in order, each from its own arena block.
        let first = client.send(OP_AGGREGATE, 0, LOG_INV_RATE, &signatures(&triples[..2]), RESP_CAP).unwrap();
        let second = client.send(OP_AGGREGATE, 0, LOG_INV_RATE, &signatures(&triples[2..]), RESP_CAP).unwrap();
        let (left, right) = (recv(&mut client), recv(&mut client));
        assert_eq!((left.id, right.id), (first, second));
        let (left, left_claims) = proved(left.status, &left.body);
        let (right, right_claims) = proved(right.status, &right.body);
        assert_eq!((left_claims.xmss.len(), right_claims.xmss.len()), (2, 1));

        let verify = proof_with_claims(&left, &left_claims);
        assert_eq!(call(&mut client, OP_VERIFY, 0, &verify).0, ST_OK);
        let mut fewer = left_claims.clone();
        fewer.xmss.pop();
        let (status, detail, _) = call(&mut client, OP_VERIFY, 0, &proof_with_claims(&left, &fewer));
        assert_eq!((status, detail), (ST_INVALID_PROOF, 0));

        let mut recurse = 2u32.to_le_bytes().to_vec();
        recurse.extend(proof_with_claims(&left, &left_claims));
        recurse.extend(proof_with_claims(&right, &right_claims));
        let (status, _, body) = call(&mut client, OP_RECURSE, FLAG_VERIFY_CHILDREN, &recurse);
        let (root, root_claims) = proved(status, &body);
        assert_eq!(root_claims.xmss.len(), 3);

        // The second child claims what the first proved: named by its index.
        let mut swapped = 2u32.to_le_bytes().to_vec();
        swapped.extend(proof_with_claims(&left, &left_claims));
        swapped.extend(proof_with_claims(&right, &left_claims));
        let (status, detail, _) = call(&mut client, OP_RECURSE, FLAG_VERIFY_CHILDREN, &swapped);
        assert_eq!((status, detail), (ST_INVALID_PROOF, 1));

        // A proof and a raw signature in one request.
        let mut extend = 1u32.to_le_bytes().to_vec();
        extend.extend(proof_with_claims(&left, &left_claims));
        extend.extend(signatures(&triples[2..]));
        let (status, _, body) = call(&mut client, OP_EXTEND, FLAG_VERIFY_CHILDREN, &extend);
        assert_eq!(proved(status, &body).1, root_claims);

        // The same through the proof the server keeps: no child in the payload.
        let mut extend = 0u32.to_le_bytes().to_vec();
        extend.extend(signatures(&triples[2..]));
        assert_eq!(call(&mut client, OP_EXTEND, FLAG_USE_KEPT, &extend).0, ST_BAD_REQUEST);
        let (status, _, body) = call(&mut client, OP_AGGREGATE, FLAG_KEEP_PROOF, &signatures(&triples[..2]));
        proved(status, &body);
        let (status, _, body) = call(&mut client, OP_EXTEND, FLAG_USE_KEPT, &extend);
        assert_eq!(proved(status, &body).1, root_claims);
        // Used without FLAG_KEEP_PROOF: no longer kept.
        assert_eq!(call(&mut client, OP_EXTEND, FLAG_USE_KEPT, &extend).0, ST_BAD_REQUEST);

        let mut retained = root_claims.clone();
        retained.xmss.remove(1);
        let mut narrow = proof_with_claims(&root, &root_claims);
        put_claims(&mut narrow, &retained);
        let (status, _, body) = call(&mut client, OP_VERIFY_NARROW, 0, &narrow);
        let (narrowed, narrowed_claims) = proved(status, &body);
        assert_eq!(narrowed_claims, retained);
        let verify = proof_with_claims(&narrowed, &narrowed_claims);
        assert_eq!(call(&mut client, OP_VERIFY, 0, &verify).0, ST_OK);

        // A response region too small for the proof: the size needed comes back, with no body.
        client.send(OP_VERIFY_NARROW, 0, LOG_INV_RATE, &narrow, 8).unwrap();
        let response = recv(&mut client);
        assert_eq!(response.status, ST_RESP_TOO_SMALL);
        assert!(response.resp_len > 8 && response.body.is_empty());

        assert_eq!(call(&mut client, OP_VERIFY, 0, &verify[..verify.len() - 1]).0, ST_BAD_REQUEST);
        assert_eq!(call(&mut client, 99, 0, &[]).0, ST_BAD_REQUEST);
        assert_eq!(client.send(OP_VERIFY, 0, 0, &[], ARENA_LEN + 1), Err(leanvm_sidecar_client::Full));
    }

    #[test]
    fn serves_every_op() {
        leanvm::setup();
        let path = std::env::temp_dir().join(format!("leanvm-sidecar-test-{}", std::process::id()));
        let chan = Channel::create(&path, RING_CAP, ARENA_LEN).unwrap();
        // Only the arena is addressable by a request.
        assert!(chan.read(0, 8).is_none() && !chan.in_arena(u64::MAX, 2));
        let stop = AtomicBool::new(false);
        std::thread::scope(|scope| {
            let worker = scope.spawn(|| {
                let _stop = StopOnDrop(&stop);
                client(&path);
            });
            run(&chan, &stop);
            let outcome = worker.join();
            let _ = std::fs::remove_file(&path);
            outcome.unwrap();
        });
    }
}
