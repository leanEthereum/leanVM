# leanvm-sidecar

A long-lived leanVM prover and verifier for one client process on the same machine. The client and the sidecar share one file on tmpfs: payloads sit in an arena inside it, and two rings of 64-byte messages carry requests and responses. The client can be written in any language that can map a file and do an atomic 64-bit load and store.

It serves four operations, on leanXMSS signatures only:

| op | what it does |
| --- | --- |
| `AGGREGATE` | prove a batch of `(pubkey, message, signature)` |
| `RECURSE` | prove the union of up to 16 proofs' claims |
| `VERIFY` | check a proof against its claims |
| `VERIFY_NARROW` | check a proof, then prove a subset of its claims |

[`PROTOCOL.md`](PROTOCOL.md) is the byte-level specification: the file layout, the messages, the payload encodings and the status codes.

## Build and run

Release only: the guest compiler overflows the debug stack.

```bash
cargo build --release -p leanvm-sidecar
target/release/leanvm-sidecar --path /dev/shm/leanvm --threads 16
```

The sidecar builds the guest, runs its warm-up, creates the channel file and prints `serving <path>`. The file appears only once it is ready, so a client may open it as soon as it exists. Stop the sidecar with a signal; it holds no state to flush.

| flag | default | meaning |
| --- | --- | --- |
| `--path` | required | the channel file; put it on tmpfs (`/dev/shm`) |
| `--threads` | one per physical core | prover threads; verification always runs on one |
| `--arena-mib` | 64 | arena size; the payload and the response region of every request in flight have to fit |
| `--ring-cap` | 64 | slots in each ring, a power of two |
| `--warmup-signatures` | 1500 | signatures in the warm-up proofs; 0 skips the warm-up |
| `--warmup-rates` | `1,2` | the `log_inv_rate` values to warm up |
| `--tracing` | off | print a timing tree per request (`RUST_LOG` sets the level) |

The warm-up is the discarded pass the benchmarks run before they measure: for each rate, one aggregation, one verification and one 16-wide recursion over signatures the sidecar makes for itself. Without it the first request of each shape is slower than the rest. Set `--warmup-signatures` to the largest batch expected and `--warmup-rates` to the rates requests will ask for.

The whole file is faulted in at start, so the arena's memory is committed from then on.

Requests are served one at a time, in order. A request in flight when the sidecar stops is lost; requests still queued are served after a restart on the same file. The header's `epoch` changes on every start, which is how a client notices.

## Clients

Each client exposes the same two calls, over raw payload bytes in the encodings of `PROTOCOL.md`:

- `send(op, flags, log_inv_rate, payload, resp_cap)` copies the payload into the arena, reserves `resp_cap` bytes for the response and queues the request. It returns the request's id, or reports that the ring or the arena is full; it never blocks.
- `try_recv()` (`tryRecv` in Java, TypeScript and Nim) returns the next response with its body copied out, or nothing if the sidecar has not produced one.

| language | where | notes |
| --- | --- | --- |
| Rust | [`crates/leanvm_sidecar_client`](../../crates/leanvm_sidecar_client) | depends on `libc` alone; links nothing of the prover |
| Go | [`clients/go`](clients/go) | package `leanvmsidecar`, standard library only |
| Java | [`clients/java`](clients/java) | `leanvmsidecar.Client`, Java 17 or later, no dependencies; channel files under 2 GiB |
| TypeScript | [`clients/typescript`](clients/typescript) | Node 18 or later; `client.ts` plus a small C addon (`mmap.c`) that maps the file, since Node cannot; `./build.sh` builds both into `dist/` |
| Nim | [`clients/nim`](clients/nim) | module `leanvmsidecar`, standard library only; needs the GCC or Clang backend for the atomics; the entry point is `openClient` |

A client is for one thread at a time. Open one only while no request of an earlier client is outstanding: the sidecar would write that request's response into arena space the new client hands out again.

The clients build no payloads and parse no bodies. The end-to-end runners below are the worked example in each language: `crates/leanvm_sidecar_client/examples/e2e.rs`, `clients/go/e2e/main.go`, `clients/java/leanvmsidecar/E2e.java`, `clients/typescript/e2e.ts` and `clients/nim/e2e.nim`.

## End-to-end test

```bash
bins/leanvm-sidecar/e2e.sh <rust|go|java|ts|nim> <threads> [aggregate-log-inv-rate=2] [recurse-log-inv-rate=1]
```

The script builds the sidecar and the chosen language's runner, starts the sidecar with `<threads>` prover threads, and has the runner make sixteen `AGGREGATE` requests of 1500 signatures each, one after the other, then one `RECURSE` over the sixteen proofs. Each step prints its request, its response and the time from `send` to the response, as the client sees it. The script stops the sidecar and removes the channel file when the runner exits.

```bash
bins/leanvm-sidecar/e2e.sh go 16        # Go client, 16 threads, default rates
bins/leanvm-sidecar/e2e.sh java 32 1 2  # Java client, aggregate at rate 1, recurse at rate 2
```

The signatures are `testdata/signatures-24000.bin`: 24000 records of `pubkey | message | signature`, every record a different signer, signer `i` on message `i mod 4`. The signers are mock keys, real only at the leaf index they sign at; their signatures verify like any other. If the file is missing the script regenerates it with `examples/gen_signatures.rs`, which takes a minute or two.

The Go runner needs `go` on `PATH`. The Java runner uses `javac` and `java` if they are on `PATH`, and otherwise the `eclipse-temurin:21-jdk` image through `docker`. The TypeScript runner needs `node`, `npm` and a C compiler: the script runs `clients/typescript/build.sh`, which installs the TypeScript compiler from npm on first use. The Nim runner uses `nim` if it is on `PATH`, and otherwise builds and runs in the `nimlang/nim:2.2.0` image through `docker`.

## Tests

```bash
cargo test --release -p leanvm-sidecar -p leanvm_sidecar_client
(cd bins/leanvm-sidecar/clients/go && go test ./...)
(cd bins/leanvm-sidecar/clients/typescript && ./build.sh && npm test)
nim c -r --outdir:target/leanvm-sidecar bins/leanvm-sidecar/clients/nim/leanvmsidecar.nim
```

The sidecar's test runs every op, and its failure cases, through the Rust client against the serving loop in one process.
