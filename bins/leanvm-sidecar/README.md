# leanvm-sidecar

Generates and verifies leanVM proofs, in a dedicated process, communicating with your client (in any langage) over a Unix socket.

## Running

```bash
cargo build --release -p leanvm-sidecar --features experimental_prover
mkdir -p -m 700 ~/.leanvm
target/release/leanvm-sidecar --socket ~/.leanvm/sidecar.sock
```

Built so, it runs the experimental prover; without `--features experimental_prover`, the stable one (the same proofs, slower).

| flag | default | meaning |
| --- | --- | --- |
| `--socket` | required | the socket to listen on, in a directory that exists |
| `--threads` | 0 | thread count, 0 for one per core |
| `--exit-with-stdin` | off | exit when standard input closes, so a program that launches it through a pipe stops it by exiting |
| `--version` | | print its release (between releases, the last one) and prover |

- It warms up (two discarded proofs) before listening, so the socket appears once it is ready. It logs to standard error.
- One sidecar per socket: it locks `<socket>.lock`, and replaces a stale socket left by one that stopped.
- The socket takes the process's umask, and connecting needs write permission on it: let only trusted clients connect, since any of them can keep it proving. Put it in a directory only the sidecar's user can write (not `/tmp`).
- It serves 16 connections at once, and closes another before its hello, so that its client fails rather than wait.
- Requests are proven one at a time, in the order they arrive. Closing the connection drops a request whose proof has not started.
- Stop it with a signal; requests in flight are lost.

## Clients

From Rust, with `lean_vm = { features = ["sidecar"] }`, the client neither proves nor verifies itself: `lean_vm::sidecar::Client` does both, with the library's arguments, blobs as they are and proofs as bytes:

```rust
let socket = std::path::Path::new(&std::env::var("HOME")?).join(".leanvm/sidecar.sock");
let mut sidecar = lean_vm::sidecar::Client::connect(socket)?;
let (claims, proof) = sidecar.aggregate(&children, &raw_lean_xmss, &[], &[], OutputClaims::All, 2)?;
assert!(sidecar.verify(&claims, &proof)?);
```

A call waits as long as the sidecar takes, unless `set_timeout` bounds it; after a timeout, drop the client.

The language bindings in [`bindings/`](../../bindings/README.md#sidecar) (Python, Node.js, Java, Go, Zig, Nim) aggregate and verify through this client too, and can launch the sidecar themselves. From another language, implement the protocol below.

## Protocol, version 1

Integers are little-endian. A **frame** and a **bytes** field are a `u64` length, then that many bytes; a **count** is a `u64`.

On connecting, the client reads a hello frame (a sidecar already serving 16 connections closes the connection instead), then sends request frames, reading each one's response before sending the next. A connection whose writing half is shut down counts as closed.

### Hello

| field | type | value |
| --- | --- | --- |
| magic | 8 bytes | `leanvmsc` |
| version | `u32` | 1 |
| max request | `u64` | the longest request body taken, 64 MiB |
| verifier | bytes | the verifier's tag, `leanvm-v1` |
| prover | bytes | `stable` or `experimental` |

The magic and the version come first in every version. A client checks them and the verifier tag, and sends no request body longer than the max request.

### Requests

**Aggregate**, the library's `aggregate`:

| field | type | meaning |
| --- | --- | --- |
| operation | `u8` | 1 |
| rate | `u8` | `log_inv_rate`, 1 to 4 |
| children | count, then per child: claims (bytes), proof (bytes) | at most 16 |
| leanXMSS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (2404 bytes) | |
| leanSPHINCS signatures | count, then per signature: pubkey (32 bytes), message (32 bytes), signature (7740 bytes) | |
| blobs | count, then per blob: 8192 symbols, each a `u128` | at most 32 |
| output | `u8`, then for 1 the claims (bytes) | 0: every covered claim; 1: exactly these |

Keys, signatures and proofs are the libraries' `to_bytes`. Signatures may come in any order, and a repeated claim counts once. Children are not verified: an invalid one fails the proof (status 3 or 4), so verify untrusted children first.

**Verify**, `AggregateProof::verify`, answered without waiting for proofs in progress:

| field | type |
| --- | --- |
| operation | `u8`, 2 |
| claims | bytes |
| proof | bytes |

**Claims**, `AggregateClaims::to_bytes`:

| field | type |
| --- | --- |
| leanXMSS claims | count, then per claim: pubkey (32 bytes), message (32 bytes) |
| leanSPHINCS claims | count, then per claim: pubkey (32 bytes), message (32 bytes) |
| DA commitment | `u8`: 0, or 1 then the root (32 bytes) |

A proof verifies only against claim lists strictly sorted by their 64 bytes; a response's claims are. Output claims may come in any order.

### Response

| field | type | meaning |
| --- | --- | --- |
| status | `u8` | below |
| for 0, to `aggregate` | claims (bytes), proof (bytes) | what the proof proves, and the proof |
| for 0, to `verify` | `u8` | 1 if the proof proves the claims, else 0 (also for a proof that does not decode) |
| otherwise | bytes | a UTF-8 message |

| status | name | meaning |
| --- | --- | --- |
| 0 | ok | |
| 1 | invalid input | a rate out of range, too many children or blobs, nothing to publish, an output claim not covered |
| 2 | invalid signature | |
| 3 | invalid child | a child is invalid, or its proof does not decode |
| 4 | proving failed | an invalid input the checks missed, or too large for one proof |
| 5 | malformed | the request does not decode, or exceeds the max request |

A request with several problems gets the first one found; `verify` gets only 0 or 5. The connection stays usable after any response but to a request over the max request, which is refused unread and closes it.
