# leanvm-sidecar protocol, version 1

`leanvm-sidecar` serves leanXMSS aggregation, recursion and verification to one client process over one shared file. The server creates the file; the client opens it read-write and maps all of it `MAP_SHARED`. Every integer is little-endian. Every offset is in bytes from the start of the file.

Clients that implement this document: `crates/leanvm_sidecar_client` (Rust), `clients/go`, `clients/java`, `clients/typescript` and `clients/nim`. Each exposes `send`, which places a payload in the arena and queues its request, and `try_recv`, which returns the next response if there is one.

The file holds a header, a request ring, a response ring and an arena. Payloads live in the arena; the rings carry 64-byte messages that point into it.

## Header

Twelve `u64` words at offset 0. The client reads them once after mapping; only `epoch` changes afterwards.

| offset | field | meaning |
| --- | --- | --- |
| 0 | `magic` | the ASCII bytes `LEANVMSH` |
| 8 | `version` | 1 |
| 16 | `epoch` | incremented each time the server starts |
| 24 | `ring_cap` | slots in each ring, a power of two |
| 32 | `total` | file size |
| 40 | `req_ring` | offset of the request ring |
| 48 | `resp_ring` | offset of the response ring |
| 56 | `arena_off` | offset of the arena |
| 64 | `arena_len` | arena size, `total - arena_off` |
| 72 | `pub_key_size` | bytes in a leanXMSS public key |
| 80 | `message_len` | bytes in a message |
| 88 | `sig_size` | bytes in a leanXMSS signature |

A client checks `magic` and `version` and takes every other number from the header.

A request in flight when the server stops is lost. A client that reads a different `epoch` than the one it saw when it sent a request stops waiting for that request and sends it again. Requests still queued in the request ring survive a restart and are served.

## Rings

Each ring is single-producer, single-consumer: the client produces requests and consumes responses, the server the reverse. A client with several threads serializes its own access.

| offset in ring | field |
| --- | --- |
| 0 | `head`, `u64`: messages consumed, written only by the consumer |
| 64 | `tail`, `u64`: messages produced, written only by the producer |
| 128 | `ring_cap` slots of 64 bytes |

Both counters only grow. Message `i` is in slot `i mod ring_cap`.

- Produce: read `tail` and `head`. If `tail - head == ring_cap` the ring is full: wait and retry. Otherwise write the message to slot `tail mod ring_cap`, then store `tail + 1`.
- Consume: read `head` and `tail`. If they are equal the ring is empty. Otherwise read slot `head mod ring_cap`, then store `head + 1`.

`head` and `tail` are read and written with atomic 64-bit operations, and the store that follows a slot access must be a releasing (or sequentially consistent) store: `sync/atomic` in Go, a `VarHandle` `getVolatile`/`setVolatile` on the mapped buffer in Java. There is no wake-up primitive. Both sides poll; the server polls an empty request ring every 100 microseconds.

## Arena

The server never allocates in the arena. The client places each request's payload wherever it likes and names, in the request, a second region for the response. The client alone decides when a region is free again: a request's two regions are the server's from the moment the request is produced until its response is consumed.

The server copies the payload out before decoding it, so a client may not rely on the server seeing a later write.

## Messages

Request, 64 bytes:

| offset | field | meaning |
| --- | --- | --- |
| 0 | `id` `u64` | echoed in the response |
| 8 | `op` `u32` | below |
| 12 | `flags` `u32` | below |
| 16 | `req_off` `u64` | payload region |
| 24 | `req_len` `u64` | |
| 32 | `resp_off` `u64` | response region |
| 40 | `resp_cap` `u64` | its capacity |
| 48 | `log_inv_rate` `u32` | PCS rate of the proof to make, 1 through 4; higher is a smaller proof and slower proving. Ignored by `VERIFY` |
| 52 | zero | |

Response, 64 bytes:

| offset | field | meaning |
| --- | --- | --- |
| 0 | `id` `u64` | the request's |
| 8 | `status` `u32` | below |
| 12 | `detail` `u32` | depends on `status` |
| 16 | `resp_len` `u64` | bytes written at `resp_off`, except under `RESP_TOO_SMALL` |
| 24 | zero | |

Both regions must lie inside the arena. Responses come in request order.

## Payloads

Building blocks:

- `claims` := `n u32 | n x (pubkey | message)`. An aggregate's claims are strictly sorted on the bytes of `pubkey | message`, with no duplicate; a proof is rejected against claims that are not.
- `proof` := `len u64 | len bytes`. The bytes are opaque to the client. A proof carries no claims: the two always travel together.
- `signatures` := `n u32 | n x (pubkey | message | signature)`, in any order. A repeated `(pubkey, message)` counts once.

| op | name | request payload | response body |
| --- | --- | --- | --- |
| 1 | `AGGREGATE` | `signatures` | `proof \| claims` |
| 2 | `RECURSE` | `n u32 \| n x (claims \| proof)` | `proof \| claims` |
| 3 | `VERIFY` | `claims \| proof` | empty |
| 4 | `VERIFY_NARROW` | `claims \| proof \| claims` | `proof \| claims` |
| 5 | `EXTEND` | `n u32 \| n x (claims \| proof) \| signatures` | `proof \| claims` |

- `AGGREGATE` proves that every signature is valid. The signatures are assumed valid: an invalid one fails the whole request with `AGGREGATION_FAILED`, without saying which.
- `RECURSE` proves the union of its children's claims. With flag `VERIFY_CHILDREN` (bit 0) the server verifies each child first and reports the first bad one as `INVALID_PROOF` with its index. Without it the client asserts the children are verified; a bad child then fails the request late as `AGGREGATION_FAILED`, usually without its index.
- `VERIFY` checks a proof against the claims given. `OK` means exactly these public keys signed exactly these messages.
- `VERIFY_NARROW` verifies the proof against the first claims, then makes a proof of the second claims, which must be a subset of the first.
- `EXTEND` is `RECURSE` and `AGGREGATE` in one proof: it proves the union of its children's claims and the signatures' claims. `VERIFY_CHILDREN` and the rules for signatures apply as in those two.

`RECURSE` and `EXTEND` take 1 to 16 children, the kept proof included.

| flag | bit | ops | meaning |
| --- | --- | --- | --- |
| `VERIFY_CHILDREN` | 0 | `RECURSE`, `EXTEND` | verify each child in the payload before proving |
| `KEEP_PROOF` | 1 | every op but `VERIFY` | the server keeps the proof it returns, in place of any it held |
| `USE_KEPT` | 2 | `RECURSE`, `EXTEND` | the kept proof is one more child, after those in the payload, which may then be none |

The server holds at most one kept proof, in memory. It lets a client grow a proof over several `EXTEND` requests without sending it back each time: `AGGREGATE` with `KEEP_PROOF`, then `EXTEND` with `USE_KEPT | KEEP_PROOF` and a payload of `0 u32 | signatures`, and the last `EXTEND` with `USE_KEPT` alone. A request with `USE_KEPT` that succeeds ends the keeping of that proof, so without `KEEP_PROOF` nothing is kept afterwards. A request that fails changes nothing, and `USE_KEPT` with nothing kept is `BAD_REQUEST`. A proof that did not fit its response region (`RESP_TOO_SMALL`) is kept all the same. The kept proof is never verified again, and a server restart loses it.

The response body repeats the claims because the server sorts and deduplicates them.

## Status

| status | name | `detail` | body |
| --- | --- | --- | --- |
| 0 | `OK` | 0 | the op's response |
| 1 | `BAD_REQUEST` | 0 | text |
| 2 | `RESP_TOO_SMALL` | 0 | nothing; `resp_len` is the capacity needed |
| 3 | `INVALID_PROOF` | index of the proof in the request | text |
| 4 | `AGGREGATION_FAILED` | reason, below | text |

`BAD_REQUEST` is a region outside the arena, an unknown op, or a payload that does not decode or has trailing bytes. The text of a failure is UTF-8 for a human, cut to `resp_cap`, possibly inside a character.

`RESP_TOO_SMALL` is found only after the proof is made, and the proof is discarded: size the response region generously.

`AGGREGATION_FAILED` reasons: 1 invalid child, 2 nothing to prove, 3 a retained claim is not among the proof's, 4 a signature does not decode, 5 too many children, 9 `log_inv_rate` out of range, 10 a child proof too large to recurse on, 11 proving failed (an invalid signature or child, or too many signatures for one proof). 6 through 8 concern blobs, which this protocol does not carry.
