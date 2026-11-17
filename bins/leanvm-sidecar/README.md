# leanvm-sidecar

A process that proves for clients on the same machine, over a Unix stream socket. It runs the library's one proving call, `aggregate`, so a client in any language gets the prover's full speed, with its own allocator, thread pool and retained memory, in a process of its own. Verifying stays in the client, with the library (`AggregateProof::verify`), which is fast and needs no prover: from another language, through a binding to it.

## Running

```bash
cargo build --release -p leanvm-sidecar
target/release/leanvm-sidecar --prover experimental --socket /run/leanvm/sidecar.sock
```

| flag | default | meaning |
| --- | --- | --- |
| `--prover` | required | `stable` or `experimental`: both give the same proofs, experimental faster |
| `--socket` | required | the socket to listen on |
| `--max-request-mib` | 1024 | the longest request taken, in MiB |
| `--threads` | 0 | the prover's thread count, 0 for one per core |
| `--tracing` | off | print each proof's timing tree (`RUST_LOG` sets the level) |

- The sidecar starts the prover's thread pool and compiles the aggregation program before it listens, so the socket appears once it is ready. It says so on standard error, then logs one line per request there.
- A sidecar holds a lock on the file beside its socket, the socket's path with `.lock` appended, while it runs. A second sidecar on the same socket fails at once. A socket left by a sidecar that stopped is replaced; a path that is some other file, or a socket another program listens on, is not.
- The socket takes the process's umask, and connecting needs write permission on it. Restrict it to the clients the sidecar serves: it trusts them with its resources. Any of them can keep it proving, and every connection may hold a request up to the max request in memory.
- Requests are proven one at a time, across all connections, in the order they are received in full. A request whose client disconnects before its proof starts is dropped; one already proving finishes, and its proof is dropped. A client that gives up on a request should therefore close its connection, and send the request again, if at all, on a new one.
- Stop the sidecar with a signal: it holds nothing to save. A request in flight is lost, and its client sees the connection close. The same goes if the prover panics, which exits the process: run the sidecar under a supervisor that restarts it.
- The first proof of a fresh sidecar is a little slower than the next ones.

## Clients

From Rust, `lean_vm::sidecar::Client` speaks the protocol, with the library's arguments but for the blobs, which go as they are:

```rust
let mut sidecar = lean_vm::sidecar::Client::connect("/run/leanvm/sidecar.sock", None)?;
let (claims, proof) = sidecar.aggregate(&children, &raw_lean_xmss, &[], &[], OutputClaims::All, 2)?;
```

`connect`'s timeout, which `Client::set_timeout` changes, bounds how long each read or write waits; after a timeout, drop the client. The client checks that the claims it gets back are those asked for, but for the DA root of blobs, which it only checks is there.

From another language, a client is the protocol below: connect, read the hello, then write a request and read its response, as many times as needed.

## Protocol, version 1

Every integer is little-endian. A **frame** is a `u64` length, then that many bytes of body. A **bytes** field is a `u64` length, then that many bytes. A **count** is a `u64`.

On each connection the sidecar first sends a hello frame. The client then sends request frames, and after each one reads a response frame before sending the next. Shutting down only the writing half of the connection counts as closing it: the sidecar drops a request it has not started proving.

### Hello

| field | type | value |
| --- | --- | --- |
| magic | 8 bytes | `leanvmsc` |
| version | `u32` | 1 |
| max request | `u64` | the longest request body the sidecar takes |
| verifier | bytes | the verifier's version tag, `leanvm-v1` |
| program | 32 bytes | the aggregation program's Fiat-Shamir IV, `Bytecode::fiat_shamir_iv` |
| prover | bytes | `stable` or `experimental` |

Every version keeps the magic and the version first. A client checks them, the verifier tag and the program, and disconnects if any differs from what it expects: a proof for another verifier or another build's program does not verify with its library. A client must not send a request body longer than the max request: the sidecar would close the connection without reading it, and the client could fail mid-write.

### Request

The library's `aggregate` arguments:

| field | type | meaning |
| --- | --- | --- |
| operation | `u8` | 1, `aggregate` |
| rate | `u8` | `log_inv_rate`, 1 to 4: higher gives a smaller proof, slower |
| children | count, then per child: claims (bytes), proof (bytes) | at most 16 |
| leanXMSS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (2404 bytes) | |
| leanSPHINCS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (7740 bytes) | |
| blobs | count, then per blob: 8192 symbols of 16 bytes each | at most 32 |
| output | `u8`, then for 1 the claims (bytes) | 0: every covered claim; 1: exactly these claims, each covered by the inputs |

Keys, signatures and proofs are the libraries' byte forms (`to_bytes`), and a symbol is its 128 bits as a little-endian `u128`, as LeanDA hashes it. Signatures may come in any order, and a repeated claim, the same pubkey and message twice, counts once. As with the library, the sidecar does not verify children: an invalid one costs a failed proof, status 3 or 4, so a child from an untrusted source is checked with `AggregateProof::verify` first.

**Claims**, as `AggregateClaims::to_bytes` writes them:

| field | type |
| --- | --- |
| leanXMSS claims | count, then per claim: pubkey (32 bytes), message (32 bytes) |
| leanSPHINCS claims | count, then per claim: pubkey (32 bytes), message (32 bytes) |
| DA commitment | `u8`, 0 for none or 1, then for 1 the root (32 bytes) |

A proof verifies only against claims whose lists are strictly sorted, comparing each claim's 64 bytes, pubkey then message, as a byte string. The claims a response carries are; the output claims of a request may come in any order.

### Response

| field | type | meaning |
| --- | --- | --- |
| status | `u8` | below |
| for 0: claims, proof | bytes, bytes | what the proof proves, and the proof (`AggregateProof::from_bytes` reads it) |
| otherwise: message | bytes | UTF-8, why there is no proof |

| status | name | meaning |
| --- | --- | --- |
| 0 | ok | |
| 1 | invalid input | the request is inconsistent: a rate out of range, too many children or blobs, nothing to publish, an output claim the inputs do not cover |
| 2 | invalid signature | a signature is invalid |
| 3 | invalid child | a child is invalid, or its proof does not decode |
| 4 | proving failed | an input the checks above missed is invalid, or the request is too large for one proof |
| 5 | malformed | the request does not decode, or is longer than the hello's max request |

A request with several problems gets the status of the first one found.

After any response the connection stays usable, except after a request longer than the max request: the sidecar answers it with status 5 without reading it, then closes the connection.
