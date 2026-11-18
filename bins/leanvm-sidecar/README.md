# leanvm-sidecar

A process that proves for clients on the same machine, over a Unix stream socket. It runs the library's one proving call, `aggregate`, so a client in any language gets the prover's full speed, with its own allocator, thread pool and retained memory, in a process of its own. It also verifies proofs, so a client builds no prover at all.

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

- The sidecar starts the prover's thread pool, compiles the aggregation program and warms up before it listens, so the socket appears once it is ready. It says so on standard error, then logs one line per `aggregate` request there.
- The warm-up, two discarded proofs, makes the first proofs as fast as the next ones: without it they pay for touching the memory the prover then keeps. A proof larger than any before it still pays for its extra memory.
- A sidecar holds a lock on the file beside its socket, the socket's path with `.lock` appended, while it runs. A second sidecar on the same socket fails at once. A socket left by a sidecar that stopped is replaced; a path that is some other file, or a socket another program listens on, is not.
- Put the socket in a directory only the sidecar's user can write, such as `/run/leanvm`, not `/tmp`: there another user could take its path, or its lock's, first.
- The socket takes the process's umask, and connecting needs write permission on it. Restrict it to the clients the sidecar serves: it trusts them with its resources. Any of them can keep it proving, and every connection may hold about twice the max request in memory.
- Requests are proven one at a time, across all connections, in the order they are received in full. A request whose client disconnects before its proof starts is dropped; one already proving finishes, and its proof is dropped. A client that gives up on a request should therefore close its connection, and send the request again, if at all, on a new one.
- Stop the sidecar with a signal: it holds nothing to save. A request in flight is lost, and its client sees the connection close. The same goes if the prover panics, which exits the process: run the sidecar under a supervisor that restarts it.

## Clients

From Rust, `lean_vm::sidecar::Client` speaks the protocol, with the library's arguments but for the blobs, which go as they are, and proofs, which are their bytes:

```rust
let mut sidecar = lean_vm::sidecar::Client::connect("/run/leanvm/sidecar.sock", None)?;
let (claims, proof) = sidecar.aggregate(&children, &raw_lean_xmss, &[], &[], OutputClaims::All, 2)?;
assert!(sidecar.verify(&claims, &proof)?);
```

With `lean_vm = { default-features = false }`, a client builds no prover: it proves and verifies through the sidecar alone, so it cannot verify while the sidecar is down or restarting. With the default `prover` feature, the library also proves and verifies in the client's process (`AggregateProof::from_bytes`, then `verify`), which takes a sidecar of the same leanVM build.

`connect`'s timeout, which `Client::set_timeout` changes, bounds how long each read or write waits; after a timeout, drop the client.

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

Every version keeps the magic and the version first. A client checks them and the verifier tag, and disconnects if any differs from what it expects: a proof for another verifier does not verify. The program identifies the leanVM build, whose proofs only that build's library verifies. A client must not send a request body longer than the max request: the sidecar would close the connection without reading it, and the client could fail mid-write.

### Requests

A request's first byte is its operation: 1 for `aggregate`, 2 for `verify`.

**Aggregate**, the library's `aggregate` arguments:

| field | type | meaning |
| --- | --- | --- |
| operation | `u8` | 1 |
| rate | `u8` | `log_inv_rate`, 1 to 4: higher gives a smaller proof, slower |
| children | count, then per child: claims (bytes), proof (bytes) | at most 16 |
| leanXMSS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (2404 bytes) | |
| leanSPHINCS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (7740 bytes) | |
| blobs | count, then per blob: 8192 symbols of 16 bytes each | at most 32 |
| output | `u8`, then for 1 the claims (bytes) | 0: every covered claim; 1: exactly these claims, each covered by the inputs |

Keys, signatures and proofs are the libraries' byte forms (`to_bytes`), and a symbol is its 128 bits as a little-endian `u128`, as LeanDA hashes it. Signatures may come in any order, and a repeated claim, the same pubkey and message twice, counts once. As with the library, the sidecar does not verify children: an invalid one costs a failed proof, status 3 or 4, so a child from an untrusted source is verified first.

**Verify**, whether a proof proves claims, as `AggregateProof::verify` says. It does not wait for the proofs being made.

| field | type |
| --- | --- |
| operation | `u8`, 2 |
| claims | bytes |
| proof | bytes |

A proof whose bytes do not decode is invalid; claims that do not decode make the request malformed.

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
| for 0, to `aggregate`: claims, proof | bytes, bytes | what the proof proves, and the proof (`AggregateProof::from_bytes` reads it) |
| for 0, to `verify`: valid | `u8` | 1 if the proof proves the claims, else 0 |
| otherwise: message | bytes | UTF-8, why there is no answer |

| status | name | meaning |
| --- | --- | --- |
| 0 | ok | |
| 1 | invalid input | the request is inconsistent: a rate out of range, too many children or blobs, nothing to publish, an output claim the inputs do not cover |
| 2 | invalid signature | a signature is invalid |
| 3 | invalid child | a child is invalid, or its proof does not decode |
| 4 | proving failed | an input the checks above missed is invalid, or the request is too large for one proof |
| 5 | malformed | the request does not decode, or is longer than the hello's max request |

A request with several problems gets the status of the first one found. A `verify` request gets only 0 or 5.

After any response the connection stays usable, except after a request longer than the max request: the sidecar answers it with status 5 without reading it, then closes the connection.
