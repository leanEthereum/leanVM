# XMSS high-level specification

## Field

KoalaBear (p = 2^31 - 2^24 + 1).

## Hash function

[Poseidon](https://eprint.iacr.org/2019/458), in compression mode (feedforward addition). Input: 16 field elements. Output: 8 field elements. We denote it `H`. Chain hashes, Merkle hashes, and the final WOTS-pubkey hash truncate the output to 4 field elements (`n`); the message hash, the encoding step, and the intermediate WOTS-pubkey sponge states keep the full 8 elements.

## Sizes

- `n = 4`: digest size (field elements)
- `|pp| = 4`: public parameter (field elements)
- `|randomness| = 6`: signature randomness (field elements)
- `|msg| = 32` bytes: raw message size (embedded into 9 field elements, hashed to 8, see below)
- `|tweak| = 2`: tweak (domain separation: `encoding`, `chain`, `wots_pk`, `merkle`)

## Message hashing (off-circuit)

The signed message is 32 raw bytes. It is embedded injectively into 9 field elements, then hashed with a domain separator to 8 field elements:

`msg_fe = H(1004 | limb_0 … limb_8 | 0^6)`

Everything below (the WOTS encoding, and hence the snark) operates on `msg_fe`; this hash is computed off-circuit.

Domain separators (first Poseidon lane): 1000 = WOTS secret key PRF, 1001 = public parameter PRF, 1002 = random filler node PRF, 1003 = signature randomness PRF, 1004 = message hash. The window [336, 1024) cannot collide with any tweak first lane.

## WOTS (Winternitz One Time Signature)

- `v = 42`: number of hash chains
- `w = 3`, `chain_length = 2^w = 8`
- `target_sum = 184`: a WOTS encoding `(e_0, ..., e_{v-1})` is valid iff each `e_i < chain_length` and `sum(e_i) = target_sum`. The signer grinds `randomness` until the encoding is valid (avoids checksum chains).

## XMSS

`log_lifetime = 32`: a key is valid for up to `2^32` slots. `log_lifetime` corresponds to the Merkle tree height.

## Signing (derandomized)

To sign `msg` at `slot`:

1. `msg_fe = hash_message(msg)`.
2. For `attempt = 0, 1, ...`: `randomness = H(H(1003 | seed | slot | attempt) | msg_fe)`. Keep the first attempt whose WOTS encoding (step 2 of verification) is valid.
3. Walk chain `i` from its secret pre-image for `e_i` steps; the signature is `(randomness, chain_tips, merkle_proof)`.

Signing is deterministic: re-signing the same `(slot, msg)` pair returns the identical signature (and is therefore harmless). Signing two *different* messages at the same slot remains forbidden — XMSS is a stateful, synchronized scheme.

The first signature after crossing into a new bottom subtree rebuilds an `O(sqrt(R))` cache; `XmssSecretKey::prepare(slot)` can do this ahead of time, off the signing critical path.

## Verification

Inputs: public key `(merkle_root, pp)`, 32-byte message `msg`, slot `s`, signature `(randomness, chain_tips, merkle_proof)`.

1. **Hash message** (off-circuit): `msg_fe = hash_message(msg)`.
2. **Encode**: compute the 8-limb digest `D = H(H(msg_fe | randomness | tweak_encoding(s)) | pp | 0000)`. For each limb `D_i`, take the canonical representative `D_i = low + 2^24 · high` (with `low ∈ [0, 2^24)`, `high ∈ [0, 128)`) and reject if `high == 127` (equivalently `D_i == −1`). This guarantees an uniform encoding. Concatenate the 24-bit `low` parts of the 8 limbs in little-endian order to get 192 bits, then take the first `v · w = 126` bits split into `v = 42` little-endian chunks of `w = 3` bits → encoding `(e_0, ..., e_{v-1})` with each `e_i ∈ [0, chain_length)`. Reject if `sum(e_i) ≠ target_sum`.
3. **Recover WOTS public key**: for each `i`, walk chain `i` from `chain_tips[i]` for `chain_length - 1 - e_i` steps, where each step is `H(tweak_chain(i, step, s) | 00 | previous_value | pp | 0000)` truncated to `n`.
4. **Hash WOTS public key**: T-sponge with replacement over the `v` recovered chain ends, with IV `[tweak_wots_pk(s) | 00 | pp]`, ingesting two chain end digests at a time. Output is the Merkle leaf.
5. **Walk Merkle path**: for `level = 0..log_lifetime`, combine the current node with `merkle_proof[level]` (left/right determined by bit `level` of `s`) via `H(tweak_merkle(level+1, parent_index) | 00 | pp | left | right)` truncated to `n`.
6. **Check root**: accept iff the final hash equals `merkle_root`.

## Data size

- Public key: 32 bytes (`merkle_root | pp`)
- Signature: 1208 bytes (`chain_tips | randomness | merkle_proof`) -> Below IPv6 [MTU](https://fr.wikipedia.org/wiki/Maximum_transmission_unit) (1280 bytes).

## Security

target ≈ 124 bits of classical security in the ROM, and ≈ 62 bits of quantum security in the QROM, with an analysis inspired by the section 3.1 of [Tight adaptive reprogramming in the QROM](https://arxiv.org/pdf/2010.15103). TODO write the complete proof.

## Signature size

