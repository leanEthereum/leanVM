# `lean_multisig_api` Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

> **Crate renamed.** This file is named `2026-08-14-lean-sig-implementation.md` and the `git
> commit` lines below are scoped `feat(lean_sig)` / `test(lean_sig)`, because `lean_sig` was the
> working name until Task 8 renamed the crate to **`lean_multisig_api`**. The filename and those
> commit scopes are left verbatim on purpose: they are the strings that appear in `git log` and
> are how a reader finds the commits for Tasks 1-7. Every other mention here says
> `lean_multisig_api`.

**Goal:** Build `crates/lean_multisig_api`, a facade over `xmss` + `rec_aggregation` that exposes signing
and single-message aggregation over byte slices, choosing every tuning parameter internally.

**Architecture:** Five modules. `plan.rs` is a pure tree planner (fast unit tests, no prover).
`codec.rs` does length-based dispatch of the mixed input vector. `key.rs` wraps `XmssSecretKey`
as an opaque handle so its bottom-subtree cache survives across signatures. `lib.rs` holds the
four public functions; `error.rs` flattens every upstream error into one enum.

**Tech Stack:** Rust 2024, `xmss`, `rec_aggregation`, `ssz` (ethereum_ssz), `postcard`, `serde`.

**Design doc:** `docs/plans/2026-08-14-lean-sig-facade-design.md`. Read it first.

---

## Background you need

Facts established by reading the existing code. Do not re-derive these.

**`xmss` crate:**

```rust
xmss_key_gen<R: CryptoRng>(rng: &mut R, activation_slot: u64, num_active_slots: u64)
    -> Result<(XmssPublicKey, XmssSecretKey), XmssKeyGenError>
xmss_key_gen_from_seed(seed: [u8; 32], activation_slot: u64, num_active_slots: u64)
    -> Result<(XmssPublicKey, XmssSecretKey), XmssKeyGenError>
xmss_sign(secret_key: &XmssSecretKey, slot: u32, message: &[u8; 32])
    -> Result<XmssSignature, XmssSignatureError>
xmss_verify(pub_key: &XmssPublicKey, slot: u32, message: &[u8; 32], signature: &XmssSignature)
    -> Result<(), XmssVerifyError>

impl XmssSecretKey {
    fn public_key(&self) -> XmssPublicKey;
    const fn activation_slots(&self) -> std::ops::RangeInclusive<u32>;
    fn prepare(&self, slot: u32) -> Result<(), XmssSignatureError>;
}
```

`XmssPublicKey` and `XmssSignature` implement `ssz::Encode` / `ssz::Decode` with **fixed**
lengths `PUB_KEY_SSZ_LEN` (32) and `SIGNATURE_SSZ_LEN` (1208). `XmssSecretKey` implements
serde `Serialize`/`Deserialize` (seed + slot range + top tree; the cache is dropped) but
**not** SSZ. `XmssPublicKey` derives `Ord`.

**`rec_aggregation` crate:**

```rust
aggregate_single_message_signatures(
    children: &[SingleMessageAggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: [u8; 32],
    slot: u32,
    log_inv_rate: usize,
) -> Result<SingleMessageAggregateSignature, AggregationError>

verify_single_message_aggregate(sig: &SingleMessageAggregateSignature)
    -> Result<InnerVerified, ProofError>

init_aggregation_bytecode();

impl SingleMessageAggregateSignature {
    fn to_bytes(&self) -> Vec<u8>;             // postcard, includes pubkeys
    fn from_bytes(bytes: &[u8]) -> Option<Self>;
}
// sig.info.pubkeys: Vec<XmssPublicKey>   — the signer set
// sig.info.core.message / .slot
```

Constants: `MAX_RECURSIONS = 16`, `MAX_XMSS_AGGREGATED = 1 << 15`. Valid `log_inv_rate` is
`1..=4` (`MIN_WHIR_LOG_INV_RATE`..`MAX_WHIR_LOG_INV_RATE`), lower = faster proving, bigger proof.

**Three traps:**

1. `get_aggregation_bytecode()` **panics** if `init_aggregation_bytecode()` was never called,
   and `SingleMessageAggregateSignature::from_bytes` silently returns `None` in that state.
   Every public entry point must call `init_aggregation_bytecode()` first. It is a `OnceLock`,
   so this is idempotent and cheap.
2. `aggregate_single_message_signatures` computes the signer set as the sorted, deduplicated
   **union** of raw pubkeys and all children's pubkeys, and rejects it above
   `MAX_XMSS_AGGREGATED` at **every** node. Recursion does not raise that ceiling.
3. Only one proving job may run per process; a concurrent call panics. Everything is sequential.

Because aggregation sorts and dedups, `verify` returns pubkeys in `XmssPublicKey`'s `Ord`
order, which is **not** the caller's input order and **not** SSZ-byte order. Compare as sets.

---

## Task 1: Scaffold the crate

**Files:**
- Create: `crates/lean_multisig_api/Cargo.toml`
- Create: `crates/lean_multisig_api/src/lib.rs`

The root `Cargo.toml` already has `members = ["crates/*", ...]`, so no workspace edit is needed.

**Step 1: Write the manifest**

```toml
[package]
name = "lean_multisig_api"
version.workspace = true
edition.workspace = true

[lints]
workspace = true

[dependencies]
xmss.workspace = true
rec_aggregation.workspace = true
backend.workspace = true
ssz.workspace = true
postcard.workspace = true
serde.workspace = true

[dev-dependencies]
rand.workspace = true
parallel = { workspace = true, features = ["forbid-parallelism"] }
```

**Step 2: Write a placeholder lib.rs**

```rust
//! An opinionated facade over `xmss` and `rec_aggregation`.
//!
//! Every tuning parameter is chosen internally. Callers needing control over `log_inv_rate`
//! or recursion topology should use `rec_aggregation` directly.
#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod error;
pub use error::Error;
```

Create an empty `crates/lean_multisig_api/src/error.rs` so this compiles.

**Step 3: Verify it builds**

Run: `cargo build -p lean_multisig_api`
Expected: success (warnings about unused deps are fine at this stage).

**Step 4: Commit**

```bash
git add crates/lean_multisig_api
git commit -m "feat(lean_sig): scaffold facade crate"
```

---

## Task 2: The error enum

**Files:**
- Modify: `crates/lean_multisig_api/src/error.rs`

**Step 1: Write the enum**

```rust
use std::fmt::{Display, Formatter};

/// Every way a `lean_multisig_api` call can fail.
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    KeyGen(xmss::XmssKeyGenError),
    Sign(xmss::XmssSignatureError),
    Verify(xmss::XmssVerifyError),
    Aggregation(rec_aggregation::AggregationError),
    Proof(backend::ProofError),
    /// A `proof_or_sig` entry decoded as neither a signature nor an aggregate.
    MalformedEntry { index: usize },
    /// A public key blob was not `PUB_KEY_SSZ_LEN` bytes, or held non-canonical field elements.
    MalformedPublicKey { index: usize },
    /// Secret key bytes could not be deserialized.
    MalformedSecretKey,
    /// `public_keys.len()` must equal the number of raw signatures in `proof_or_sig`.
    PubkeyCountMismatch { expected: usize, got: usize },
    /// The deduplicated signer union exceeds `MAX_XMSS_AGGREGATED`.
    TooManySigners { got: usize, max: usize },
    /// `proof_or_sig` was empty.
    Empty,
    /// The proved signer set differs from the expected one.
    SignerSetMismatch,
}
```

Add `Display` with one arm per variant, then `impl std::error::Error for Error {}`, then
`From` impls for the five wrapped types so `?` works.

**Step 2: Verify**

Run: `cargo build -p lean_multisig_api`
Expected: success.

**Step 3: Commit**

```bash
git commit -am "feat(lean_sig): flattened error enum"
```

---

## Task 3: The tree planner (pure, fast tests)

This is the highest-value module to get right, and the only one testable without a prover.
Keep it free of any `rec_aggregation` calls.

**Files:**
- Create: `crates/lean_multisig_api/src/plan.rs`
- Modify: `crates/lean_multisig_api/src/lib.rs` (add `mod plan;`)

**Step 1: Write the failing tests first**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_child_alone_is_passed_through() {
        // Re-proving a lone aggregate would burn minutes for no benefit.
        assert_eq!(plan(0, 1), Plan::Passthrough(0));
    }

    #[test]
    fn small_raw_batch_is_one_node_at_root_rate() {
        // Must be RATE_ROOT, not RATE_LEAF: this node IS the wire proof.
        assert_eq!(
            plan(1, 0),
            Plan::Node { raw: 0..1, children: vec![], log_inv_rate: RATE_ROOT }
        );
        assert_eq!(
            plan(LEAF_TARGET, 0),
            Plan::Node { raw: 0..LEAF_TARGET, children: vec![], log_inv_rate: RATE_ROOT }
        );
    }

    #[test]
    fn overflowing_one_leaf_splits_and_adds_a_root() {
        let p = plan(LEAF_TARGET + 1, 0);
        let Plan::Node { raw, children, log_inv_rate } = p else { panic!("expected a node") };
        assert!(raw.is_empty());
        assert_eq!(log_inv_rate, RATE_ROOT);
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0],
            Plan::Node { raw: 0..LEAF_TARGET, children: vec![], log_inv_rate: RATE_LEAF }
        );
    }

    #[test]
    fn fan_in_never_exceeds_max_recursions() {
        for n in [1, 2, LEAF_TARGET, LEAF_TARGET * 40, MAX_XMSS_AGGREGATED] {
            assert_fan_in_ok(&plan(n, 0));
        }
    }

    fn assert_fan_in_ok(p: &Plan) {
        if let Plan::Node { children, .. } = p {
            assert!(children.len() <= MAX_FAN_IN, "fan-in {} too wide", children.len());
            children.iter().for_each(assert_fan_in_ok);
        }
    }

    #[test]
    fn every_raw_signature_is_covered_exactly_once() {
        // The planner returning index ranges makes off-by-ones silent otherwise.
        let n = LEAF_TARGET * 3 + 7;
        let mut seen = vec![0u8; n];
        collect(&plan(n, 0), &mut seen);
        assert!(seen.iter().all(|&c| c == 1), "each raw sig must appear exactly once");
    }

    fn collect(p: &Plan, seen: &mut [u8]) {
        if let Plan::Node { raw, children, .. } = p {
            for i in raw.clone() { seen[i] += 1; }
            children.iter().for_each(|c| collect(c, seen));
        }
    }

    #[test]
    fn rates_descend_toward_the_root() {
        let p = plan(LEAF_TARGET * 40, 0);
        let Plan::Node { log_inv_rate, children, .. } = &p else { panic!() };
        assert_eq!(*log_inv_rate, RATE_ROOT);
        // Every non-root internal node proves at RATE_INTERNAL, every leaf at RATE_LEAF.
        for c in children {
            if let Plan::Node { log_inv_rate, children: gc, .. } = c {
                let expected = if gc.is_empty() { RATE_LEAF } else { RATE_INTERNAL };
                assert_eq!(*log_inv_rate, expected);
            }
        }
    }
}
```

**Step 2: Run to verify they fail**

Run: `cargo test -p lean_multisig_api --lib plan`
Expected: FAIL, `cannot find function plan`.

**Step 3: Write the implementation**

```rust
use rec_aggregation::{MAX_RECURSIONS, MAX_XMSS_AGGREGATED};
use std::ops::Range;

/// Raw signatures per leaf. Taken from `src/main.rs`'s tuned topology (leaves of 508..1550),
/// bounded by the 2^22 table height. See the design doc's open questions: this wants measuring.
pub(crate) const LEAF_TARGET: usize = 1500;
pub(crate) const MAX_FAN_IN: usize = MAX_RECURSIONS;

/// Fast proving, large proof. Leaf proofs are consumed immediately, so size is irrelevant.
pub(crate) const RATE_LEAF: usize = 1;
pub(crate) const RATE_INTERNAL: usize = 2;
/// Smallest proof. Only the root goes on the wire.
pub(crate) const RATE_ROOT: usize = 4;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Plan {
    /// Return a caller-supplied aggregate unchanged; the index is into the supplied children.
    Passthrough(usize),
    Node {
        /// Range into the raw-signature vector. May be empty for internal nodes.
        raw: Range<usize>,
        children: Vec<Plan>,
        log_inv_rate: usize,
    },
}

pub(crate) fn plan(n_raw: usize, n_children: usize) -> Plan {
    // A lone aggregate is already a valid proof.
    if n_raw == 0 && n_children == 1 {
        return Plan::Passthrough(0);
    }
    // Everything fits in one node: prove it directly at the root rate.
    if n_raw <= LEAF_TARGET && n_children == 0 {
        return Plan::Node { raw: 0..n_raw, children: vec![], log_inv_rate: RATE_ROOT };
    }

    let mut pool: Vec<Plan> = (0..n_raw)
        .step_by(LEAF_TARGET)
        .map(|start| Plan::Node {
            raw: start..(start + LEAF_TARGET).min(n_raw),
            children: vec![],
            log_inv_rate: RATE_LEAF,
        })
        .collect();
    pool.extend((0..n_children).map(Plan::Passthrough));

    while pool.len() > MAX_FAN_IN {
        pool = pool
            .chunks(MAX_FAN_IN)
            .map(|group| Plan::Node {
                raw: 0..0,
                children: group.to_vec(),
                log_inv_rate: RATE_INTERNAL,
            })
            .collect();
    }

    Plan::Node { raw: 0..0, children: pool, log_inv_rate: RATE_ROOT }
}
```

Note `chunks` on a `Vec<Plan>` needs `Plan: Clone`, which the derive provides.

**Step 4: Run tests**

Run: `cargo test -p lean_multisig_api --lib plan`
Expected: PASS, 6 tests.

**Step 5: Commit**

```bash
git commit -am "feat(lean_sig): pure recursion-tree planner"
```

---

## Task 4: Codec and pubkey pairing

**Files:**
- Create: `crates/lean_multisig_api/src/codec.rs`
- Modify: `crates/lean_multisig_api/src/lib.rs` (add `mod codec;`)

**Step 1: Write the failing tests**

These need real signatures, so add a small helper. Keygen over a 16-slot range is fast
(no proving involved).

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use xmss::{xmss_key_gen_from_seed, xmss_sign};
    use ssz::Encode;

    fn sample(seed: u8) -> (Vec<u8>, Vec<u8>) {
        let (pk, sk) = xmss_key_gen_from_seed([seed; 32], 100, 16).unwrap();
        let sig = xmss_sign(&sk, 100, &[7u8; 32]).unwrap();
        (pk.as_ssz_bytes(), sig.as_ssz_bytes())
    }

    #[test]
    fn classifies_raw_signatures_by_length() {
        let (pk, sig) = sample(1);
        assert_eq!(sig.len(), xmss::SIGNATURE_SSZ_LEN);
        let (raw, aggs) = classify(vec![sig], vec![pk]).unwrap();
        assert_eq!(raw.len(), 1);
        assert!(aggs.is_empty());
    }

    #[test]
    fn rejects_a_correctly_sized_but_corrupt_signature() {
        // Must NOT silently fall through to the aggregate parser.
        let (pk, mut sig) = sample(2);
        sig[0] = 0xff; sig[1] = 0xff; sig[2] = 0xff; sig[3] = 0xff; // non-canonical field element
        assert!(matches!(
            classify(vec![sig], vec![pk]),
            Err(Error::MalformedEntry { index: 0 })
        ));
    }

    #[test]
    fn pubkey_count_must_match_raw_count() {
        let (pk, sig) = sample(3);
        let err = classify(vec![sig.clone(), sig], vec![pk]).unwrap_err();
        assert!(matches!(err, Error::PubkeyCountMismatch { expected: 2, got: 1 }));
    }

    #[test]
    fn rejects_a_wrong_length_pubkey() {
        let (_, sig) = sample(4);
        assert!(matches!(
            classify(vec![sig], vec![vec![0u8; 8]]),
            Err(Error::MalformedPublicKey { index: 0 })
        ));
    }

    #[test]
    fn empty_input_is_rejected() {
        assert!(matches!(classify(vec![], vec![]), Err(Error::Empty)));
    }
}
```

**Step 2: Run to verify failure**

Run: `cargo test -p lean_multisig_api --lib codec`
Expected: FAIL, `cannot find function classify`.

**Step 3: Implement**

```rust
use crate::Error;
use rec_aggregation::SingleMessageAggregateSignature;
use ssz::Decode;
use xmss::{PUB_KEY_SSZ_LEN, SIGNATURE_SSZ_LEN, XmssPublicKey, XmssSignature};

type Raw = (XmssPublicKey, XmssSignature);

/// Splits the mixed input vector into raw signatures (paired with their pubkeys) and
/// previously produced aggregates.
///
/// Entries are classified by length: exactly `SIGNATURE_SSZ_LEN` means a raw signature,
/// anything else is parsed as a postcard aggregate. A correctly sized blob that fails SSZ
/// decode is an error, never a fallback to the aggregate parser — silent reclassification
/// would surface as a baffling failure much later.
///
/// Aggregates carry their own signer sets, so `public_keys` covers raw signatures only:
/// the k-th raw entry pairs with `public_keys[k]`.
pub(crate) fn classify(
    proof_or_sig: Vec<Vec<u8>>,
    public_keys: Vec<Vec<u8>>,
) -> Result<(Vec<Raw>, Vec<SingleMessageAggregateSignature>), Error> {
    if proof_or_sig.is_empty() {
        return Err(Error::Empty);
    }

    let expected = proof_or_sig.iter().filter(|e| e.len() == SIGNATURE_SSZ_LEN).count();
    if expected != public_keys.len() {
        return Err(Error::PubkeyCountMismatch { expected, got: public_keys.len() });
    }

    let mut raw = Vec::with_capacity(expected);
    let mut aggregates = Vec::new();
    let mut next_pk = 0usize;

    for (index, entry) in proof_or_sig.iter().enumerate() {
        if entry.len() == SIGNATURE_SSZ_LEN {
            let sig = XmssSignature::from_ssz_bytes(entry)
                .map_err(|_| Error::MalformedEntry { index })?;
            let pk_bytes = &public_keys[next_pk];
            if pk_bytes.len() != PUB_KEY_SSZ_LEN {
                return Err(Error::MalformedPublicKey { index: next_pk });
            }
            let pk = XmssPublicKey::from_ssz_bytes(pk_bytes)
                .map_err(|_| Error::MalformedPublicKey { index: next_pk })?;
            next_pk += 1;
            raw.push((pk, sig));
        } else {
            let agg = SingleMessageAggregateSignature::from_bytes(entry)
                .ok_or(Error::MalformedEntry { index })?;
            aggregates.push(agg);
        }
    }

    Ok((raw, aggregates))
}
```

**Important:** `from_bytes` needs the bytecode initialized. Task 6 puts
`init_aggregation_bytecode()` in the public entry points; until then, codec tests must only
use raw signatures (as written above).

**Step 4: Run tests**

Run: `cargo test -p lean_multisig_api --lib codec`
Expected: PASS, 5 tests.

**Step 5: Commit**

```bash
git commit -am "feat(lean_sig): length-based entry dispatch and pubkey pairing"
```

---

## Task 5: The `SecretKey` handle

**Files:**
- Create: `crates/lean_multisig_api/src/key.rs`
- Modify: `crates/lean_multisig_api/src/lib.rs` (add `mod key; pub use key::SecretKey;`)

**Step 1: Write the failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_then_verify_round_trips() {
        let sk = SecretKey::from_seed([1u8; 32], 100, 16).unwrap();
        let sig = sk.sign(&[9u8; 32], 100).unwrap();
        assert_eq!(sig.len(), xmss::SIGNATURE_SSZ_LEN);
        assert_eq!(sk.public_key().len(), xmss::PUB_KEY_SSZ_LEN);
    }

    #[test]
    fn from_seed_is_deterministic() {
        let a = SecretKey::from_seed([2u8; 32], 100, 16).unwrap();
        let b = SecretKey::from_seed([2u8; 32], 100, 16).unwrap();
        assert_eq!(a.public_key(), b.public_key());
    }

    #[test]
    fn serialization_preserves_signing() {
        // The cache is dropped on deserialize; signatures must still be identical, since
        // signing is derandomized from (seed, slot, message).
        let sk = SecretKey::from_seed([3u8; 32], 100, 16).unwrap();
        let before = sk.sign(&[4u8; 32], 105).unwrap();
        let restored = SecretKey::from_bytes(&sk.to_bytes()).unwrap();
        assert_eq!(restored.public_key(), sk.public_key());
        assert_eq!(restored.sign(&[4u8; 32], 105).unwrap(), before);
    }

    #[test]
    fn signing_outside_the_slot_range_fails() {
        let sk = SecretKey::from_seed([5u8; 32], 100, 16).unwrap();
        assert_eq!(sk.slots(), 100..=115);
        assert!(sk.sign(&[0u8; 32], 116).is_err());
        assert!(sk.sign(&[0u8; 32], 99).is_err());
    }

    #[test]
    fn malformed_bytes_are_rejected() {
        assert!(matches!(
            SecretKey::from_bytes(&[0u8; 3]),
            Err(Error::MalformedSecretKey)
        ));
    }
}
```

**Step 2: Run to verify failure**

Run: `cargo test -p lean_multisig_api --lib key`
Expected: FAIL, `cannot find type SecretKey`.

**Step 3: Implement**

```rust
use crate::Error;
use ssz::Encode;
use xmss::{XmssSecretKey, xmss_key_gen, xmss_key_gen_from_seed, xmss_sign};

/// An XMSS secret key, active for a fixed slot range.
///
/// This is a handle rather than a byte slice on purpose: the key holds a bottom-subtree cache
/// that `sign` warms and reuses. Serializing drops that cache, so a bytes-in/bytes-out `sign`
/// would rebuild a subtree on every call.
///
/// WARNING: XMSS is stateful. Never sign two different messages at the same slot. Signing is
/// derandomized, so repeating the same (slot, message) is harmless and returns identical bytes.
#[derive(Debug)]
pub struct SecretKey(XmssSecretKey);

impl SecretKey {
    /// Generates a key active for `num_active_slots` slots starting at `activation_slot`.
    pub fn generate(activation_slot: u64, num_active_slots: u64) -> Result<Self, Error> {
        let mut rng = rand::rng();
        let (_, sk) = xmss_key_gen(&mut rng, activation_slot, num_active_slots)?;
        Ok(Self(sk))
    }

    /// Deterministic [`Self::generate`]. The seed is the key's entire secret material.
    pub fn from_seed(seed: [u8; 32], activation_slot: u64, num_active_slots: u64)
        -> Result<Self, Error>
    {
        let (_, sk) = xmss_key_gen_from_seed(seed, activation_slot, num_active_slots)?;
        Ok(Self(sk))
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        postcard::from_bytes::<XmssSecretKey>(bytes)
            .map(Self)
            .map_err(|_| Error::MalformedSecretKey)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.0).expect("postcard serialization failed")
    }

    /// SSZ-encoded public key, `PUB_KEY_SSZ_LEN` bytes.
    pub fn public_key(&self) -> Vec<u8> {
        self.0.public_key().as_ssz_bytes()
    }

    pub fn slots(&self) -> std::ops::RangeInclusive<u32> {
        self.0.activation_slots()
    }

    /// Warms the signing cache for `slot`. Worth calling when the next slot is known ahead
    /// of time; this is the one choice the library cannot make for you.
    pub fn prepare(&self, slot: u32) -> Result<(), Error> {
        self.0.prepare(slot).map_err(Into::into)
    }

    /// SSZ-encoded signature, `SIGNATURE_SSZ_LEN` bytes, ready for `aggregate`.
    pub fn sign(&self, message: &[u8; 32], slot: u32) -> Result<Vec<u8>, Error> {
        Ok(xmss_sign(&self.0, slot, message)?.as_ssz_bytes())
    }
}
```

Add `rand.workspace = true` to `[dependencies]` (it is currently only a dev-dependency).

**Step 4: Run tests**

Run: `cargo test -p lean_multisig_api --lib key`
Expected: PASS, 5 tests.

**Step 5: Commit**

```bash
git commit -am "feat(lean_sig): SecretKey handle with warm signing cache"
```

---

## Task 6: `aggregate` and `verify`

**Files:**
- Modify: `crates/lean_multisig_api/src/lib.rs`

No unit tests here — every path needs a real prover. Task 7 covers it with integration tests.

**Step 1: Implement the public functions**

```rust
use rec_aggregation::{
    MAX_XMSS_AGGREGATED, SingleMessageAggregateSignature, aggregate_single_message_signatures,
    init_aggregation_bytecode, verify_single_message_aggregate,
};
use ssz::Encode;
use std::collections::BTreeSet;

/// Pays the one-time bytecode compile up front. Optional: every entry point does this lazily.
pub fn warm_up() {
    init_aggregation_bytecode();
}

/// Aggregates raw XMSS signatures and previously produced aggregates into a single proof,
/// all sharing one `(message, slot)`.
///
/// `public_keys` covers **raw signatures only** — aggregates carry their own signer sets — so
/// the k-th raw entry of `proof_or_sig` pairs with `public_keys[k]`. The two vectors are
/// therefore not index-aligned when aggregates are present.
///
/// The recursion tree and every `log_inv_rate` are chosen internally.
///
/// Runs entirely sequentially: only one proving job may run per process, so wall-clock is the
/// sum of every node's proving time. Expect this to be slow for large inputs.
pub fn aggregate(
    proof_or_sig: Vec<Vec<u8>>,
    public_keys: Vec<Vec<u8>>,
    message: [u8; 32],
    slot: u32,
) -> Result<Vec<u8>, Error> {
    init_aggregation_bytecode();
    let (raw, children) = codec::classify(proof_or_sig, public_keys)?;

    // Reject over-capacity before proving anything: failing after minutes of work is cruel.
    let mut signers: BTreeSet<_> = raw.iter().map(|(pk, _)| pk.clone()).collect();
    for child in &children {
        signers.extend(child.info.pubkeys.iter().cloned());
    }
    if signers.len() > MAX_XMSS_AGGREGATED {
        return Err(Error::TooManySigners { got: signers.len(), max: MAX_XMSS_AGGREGATED });
    }

    let tree = plan::plan(raw.len(), children.len());
    Ok(execute(&tree, &raw, &children, message, slot)?.to_bytes())
}

fn execute(
    node: &plan::Plan,
    raw: &[(xmss::XmssPublicKey, xmss::XmssSignature)],
    children: &[SingleMessageAggregateSignature],
    message: [u8; 32],
    slot: u32,
) -> Result<SingleMessageAggregateSignature, Error> {
    match node {
        plan::Plan::Passthrough(i) => Ok(children[*i].clone()),
        plan::Plan::Node { raw: range, children: kids, log_inv_rate } => {
            let proved: Vec<_> = kids
                .iter()
                .map(|k| execute(k, raw, children, message, slot))
                .collect::<Result<_, _>>()?;
            let mine = raw[range.clone()].to_vec();
            Ok(aggregate_single_message_signatures(&proved, mine, message, slot, *log_inv_rate)?)
        }
    }
}

/// Verifies an aggregate and returns the signer set it actually proves, as SSZ-encoded
/// public keys.
///
/// The signer set is the success value rather than an input on purpose: an aggregate over the
/// wrong validator set is still a valid proof, so a `bool` would let callers forget to check
/// who signed. Order is the library's canonical sorted order, not the order you aggregated in
/// — compare as a set.
#[must_use = "an aggregate proves nothing until you check who signed it"]
pub fn verify(aggregate: &[u8], message: &[u8; 32], slot: u32) -> Result<Vec<Vec<u8>>, Error> {
    init_aggregation_bytecode();
    let sig = SingleMessageAggregateSignature::from_bytes(aggregate)
        .ok_or(Error::MalformedEntry { index: 0 })?;
    if &sig.info.core.message != message || sig.info.core.slot != slot {
        return Err(Error::SignerSetMismatch);
    }
    verify_single_message_aggregate(&sig)?;
    Ok(sig.info.pubkeys.iter().map(Encode::as_ssz_bytes).collect())
}

/// [`verify`], checking the proved signer set against one you already know.
pub fn verify_with_signers(
    aggregate: &[u8],
    expected: &[Vec<u8>],
    message: &[u8; 32],
    slot: u32,
) -> Result<(), Error> {
    let proved = verify(aggregate, message, slot)?;
    let proved: BTreeSet<_> = proved.into_iter().collect();
    let expected: BTreeSet<_> = expected.iter().cloned().collect();
    if proved == expected { Ok(()) } else { Err(Error::SignerSetMismatch) }
}
```

Note the message/slot mismatch currently reuses `SignerSetMismatch`. Add a distinct
`Error::MessageMismatch` variant instead — a wrong message is not a wrong signer set.

**Step 2: Verify it builds**

Run: `cargo build -p lean_multisig_api && cargo clippy -p lean_multisig_api --all-targets`
Expected: no warnings (the workspace denies a lot; fix what it flags).

**Step 3: Commit**

```bash
git commit -am "feat(lean_sig): aggregate and verify entry points"
```

---

## Task 7: Integration tests

**Files:**
- Create: `crates/lean_multisig_api/tests/round_trip.rs`

These invoke the real prover and are slow. Keep counts tiny.

**Step 1: Write the tests**

```rust
use lean_multisig_api::{SecretKey, aggregate, verify, verify_with_signers};
use std::collections::BTreeSet;

const MSG: [u8; 32] = [42u8; 32];
const SLOT: u32 = 100;

fn signers(n: u8) -> Vec<SecretKey> {
    (0..n).map(|i| SecretKey::from_seed([i; 32], 100, 16).unwrap()).collect()
}

#[test]
fn aggregate_then_verify_returns_the_signer_set() {
    let keys = signers(2);
    let sigs: Vec<_> = keys.iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
    let pks: Vec<_> = keys.iter().map(SecretKey::public_key).collect();

    let agg = aggregate(sigs, pks.clone(), MSG, SLOT).unwrap();

    // Aggregation sorts and dedups, so compare as sets.
    let proved: BTreeSet<_> = verify(&agg, &MSG, SLOT).unwrap().into_iter().collect();
    assert_eq!(proved, pks.iter().cloned().collect::<BTreeSet<_>>());

    verify_with_signers(&agg, &pks, &MSG, SLOT).unwrap();
}

#[test]
fn verify_rejects_the_wrong_message() {
    let keys = signers(2);
    let sigs: Vec<_> = keys.iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
    let pks: Vec<_> = keys.iter().map(SecretKey::public_key).collect();
    let agg = aggregate(sigs, pks, MSG, SLOT).unwrap();

    assert!(verify(&agg, &[0u8; 32], SLOT).is_err());
    assert!(verify(&agg, &MSG, SLOT + 1).is_err());
}

#[test]
fn verify_rejects_a_tampered_proof() {
    let keys = signers(2);
    let sigs: Vec<_> = keys.iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
    let pks: Vec<_> = keys.iter().map(SecretKey::public_key).collect();
    let mut agg = aggregate(sigs, pks, MSG, SLOT).unwrap();

    let last = agg.len() - 1;
    agg[last] ^= 0xff;
    assert!(verify(&agg, &MSG, SLOT).is_err());
}

#[test]
fn verify_rejects_a_different_expected_signer_set() {
    let keys = signers(2);
    let sigs: Vec<_> = keys.iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
    let pks: Vec<_> = keys.iter().map(SecretKey::public_key).collect();
    let agg = aggregate(sigs, pks.clone(), MSG, SLOT).unwrap();

    let outsider = SecretKey::from_seed([99u8; 32], 100, 16).unwrap().public_key();
    assert!(verify_with_signers(&agg, &[pks[0].clone(), outsider], &MSG, SLOT).is_err());
}

#[test]
fn works_without_an_explicit_warm_up() {
    // Lazy init must make the bytecode OnceLock invisible; this must not panic.
    let keys = signers(1);
    let sigs = vec![keys[0].sign(&MSG, SLOT).unwrap()];
    let pks = vec![keys[0].public_key()];
    let agg = aggregate(sigs, pks, MSG, SLOT).unwrap();
    verify(&agg, &MSG, SLOT).unwrap();
}

#[test]
#[ignore = "slow: builds a multi-level recursion tree"]
fn multi_level_tree_round_trips() {
    // Feed a prior aggregate back in alongside fresh raw signatures.
    let keys = signers(3);
    let first: Vec<_> = keys[..2].iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
    let first_pks: Vec<_> = keys[..2].iter().map(SecretKey::public_key).collect();
    let inner = aggregate(first, first_pks, MSG, SLOT).unwrap();

    let outer = aggregate(
        vec![inner, keys[2].sign(&MSG, SLOT).unwrap()],
        vec![keys[2].public_key()],   // raw signatures only — the aggregate carries its own
        MSG,
        SLOT,
    ).unwrap();

    let proved = verify(&outer, &MSG, SLOT).unwrap();
    assert_eq!(proved.len(), 3);
}
```

### Required: the assertions Task 4 could not make

`codec::classify` has two coverage holes that are impossible to close at unit level, because
building a parseable aggregate needs both the bytecode `OnceLock` populated and a real
`ExecutionProof`. Both must be closed here, and `multi_level_tree_round_trips` is the natural
home since it already feeds an aggregate back in:

1. **No test has ever observed `classify` return successfully with a non-raw entry present** —
   the `aggregates` vector has never been seen non-empty. Assert that folding a real aggregate
   together with fresh raw signatures both succeeds *and* yields the union of signers, not just
   that it returns `Ok`. Note pairing-by-raw-order is structural in the `zip`, so this is
   confirming an untested path rather than guarding a fragile one.

2. **`rejects_a_correctly_sized_but_corrupt_signature` cannot discriminate what its name says.**
   A hypothetical fall-through to the aggregate parser produces the identical error at unit
   level, since `from_bytes` returns `None` with no bytecode initialized. Fall-through is
   prevented by construction (the `if`/`else` in `classify`), but with the bytecode genuinely
   initialized here, a corrupt 1208-byte blob can be shown to give `MalformedSignature` rather
   than `MalformedEntry` — which does discriminate.

Since this test is `#[ignore]`d, run it manually at least once and record that you did.

### Correction (Task 8): the multi-level tree is neither ignored nor impractical

**The paragraphs above are wrong about cost, and were wrong when written.** They assume a real
multi-level tree is unaffordable and gate `multi_level_tree_round_trips` behind `#[ignore]`.
Tree depth does not come from `LEAF_TARGET`; it comes from **fan-in** (`MAX_FAN_IN =
MAX_RECURSIONS = 16`). Reaching depth 3 through raw signatures alone would need `1500 * 17` of
them, which is indeed not a test at any budget — but 17 *supplied children* fold into an
internal node over 16 plus a leftover, which is a three-level tree for 19 small proving jobs in
**~8s release**.

As built, `a_multi_level_tree_round_trips` takes 17 single-signer children, is **not**
`#[ignore]`d, and runs in CI with everything else. It is the only test that exercises the
planner's `while pool.len() > MAX_FAN_IN` fold loop, and with it the only `Passthrough` under a
*non-root* node — so gating it would have left the planner's most interesting branch unproved.
It is still the most expensive default test in the file and the first place to look if that
binary's runtime becomes a problem.

The two tests that *are* `#[ignore]`d are the `LEAF_TARGET` boundary pair added later
(`a_leaf_target_sized_batch_proves`, `a_batch_one_past_leaf_target_splits_and_proves`), and CI
runs those too, in a scoped `Ignored slow tests` step.

The coverage holes 1 and 2 above are genuine and were closed — but in
`folding_an_aggregate_with_fresh_signatures_unions_the_signers` and
`a_corrupt_signature_sized_blob_is_a_malformed_signature_not_a_malformed_entry` respectively,
both of which run by default.

**Step 2: Run**

Run: `cargo test -p lean_multisig_api --test round_trip`
Expected: 5 pass, 1 ignored. Expect minutes, not seconds.
*As built:* 12 pass, 2 ignored, ~11s in release (~317s in debug). The "minutes" estimate was
for debug; use `--release`.

If a small signer count trips a prover edge case, raise the count rather than shrinking the
test, and record the working count in the design doc's open questions.

**Step 3: Run the ignored one once manually**

Run: `cargo test -p lean_multisig_api --test round_trip -- --ignored`
Expected: PASS. *As built:* this runs the two `LEAF_TARGET` boundary tests, not the multi-level
one, and CI runs it too — see Task 8. The mixed raw+aggregate input path is covered by a
default test.

**Step 4: Commit**

```bash
git commit -am "test(lean_sig): round-trip and negative integration tests"
```

---

## Task 8: Rename, CI, and final verification

Task 8 also renamed the crate from `lean_sig` to `lean_multisig_api` and added a scoped CI step
for the two `#[ignore]`d `LEAF_TARGET` boundary tests. See `.github/workflows/rust.yml`'s
`Ignored slow tests` step; note `--verbose` has to go *before* the `--`, since libtest rejects
it (`error: Unrecognized option: 'verbose'`) and would fail the step before running anything.

**Step 1: Full workspace**

Run: `cargo test --workspace --lib --no-fail-fast`
Expected: 0 failures across all targets.
*As built:* run without `--lib` and in release — `cargo test --release --workspace
--no-fail-fast` — since `--lib` skips every integration binary, which is where this crate's
proving tests live. Result: 130 passed, 0 failed, 18 ignored.

**Step 2: Lints and formatting**

Run: `cargo clippy --workspace --all-targets && cargo fmt --all -- --check`
Expected: clean.
*As built:* `-Dwarnings` added to match CI, plus a pedantic/nursery pass over this crate alone.

**Step 3: Docs**

Run: `cargo doc -p lean_multisig_api --no-deps`
Expected: no warnings (`rustdoc.all = "warn"` is set workspace-wide).

**Step 4: Two decisions carried over from Task 6**

*Move the wire-format fixture upstream.* `tests/unprovable_child.rs` hand-encodes
`SingleMessageAggregateSignature`'s postcard layout, exploiting the fact that a tuple of the
right leaves is byte-identical to a struct whose fields are `pub(crate)` and unconstructable
from outside. `the_fixture_really_does_get_past_the_envelope` keeps it from silently going
vacuous, which is what makes the technique safe — but the knowledge lives in the wrong crate.
A `rec_aggregation` `test-utils` feature exposing a constructor for a structurally valid,
unprovable aggregate would put it where a field reorder is a compile error instead of a
downstream fixture that parses by luck. `xmss` already gates `signers_cache` this way, so the
pattern exists. Decide whether to do it here or file it as follow-up.

**DECIDED: defer, filed as follow-up** in the design doc's "Follow-up" section. Three reasons.
(1) It changes `rec_aggregation`'s public surface — a new feature and a new exported
constructor — which is outside the scope of a facade whose whole premise is depending on
`rec_aggregation` rather than reshaping it. (2) The stated risk is bounded today:
`the_fixture_really_does_get_past_the_envelope` asserts that the blob parses far enough to
reach `MessageMismatch`, so a field reorder upstream turns the two real tests from
"passing for the right reason" into a *failing* guard test, not a silently vacuous suite. The
failure would be confusing rather than invisible, which is a much smaller problem than the one
the move is meant to solve. (3) It is not cheap. A useful upstream constructor has to keep the
"structurally valid but unprovable" property, which means it also has to know
`cumulated_n_vars()` and `check_single_message_pubkeys`'s requirements — the same knowledge,
relocated, plus a feature flag and its CI configuration. Worth doing when `rec_aggregation` is
next opened for its own reasons; not worth opening it for.

*Decide whether `lazy_init_verify_with_signers` earns its ~24s.* All three lazy-init binaries
are separate files purely so each gets its own process — a shared one would let one test's
init satisfy another's assertion. But they are not equal value: the `aggregate` and `verify`
ones pin ordering claims no other test can observe, while this one pins that a four-line
function calls `verify` first, which is visible by reading it. With Task 7's costs now on the
table, decide once whether to keep, `#[ignore]`, or drop it.

**DECIDED: keep, unchanged.** The ~24s was a debug figure and the premise it rested on is
gone. Measured in release, the binary costs **2.83s** — and the other two lazy-init binaries
cost 2.83s each as well, so this is not the expensive one; all three are dominated by the same
one-time bytecode compile. A cost-based argument for singling it out no longer exists.

The value argument stands as written — it is the weakest of the three — but "weakest of three"
is not "worthless". `verify_with_signers` calling `verify` first is visible by reading it
*today*; the test is what keeps it true after someone adds a length or set-size pre-check
above that call, which is exactly the plausible edit that would move a public entry point back
in front of the `OnceLock`. At 2.83s for a claim about a public entry point fed by gossip, and
with the alternative being an asymmetry a reader would have to be told about, keeping it is
the cheaper option in every sense that was actually measured.

**Step 5: Update the design doc**

Resolve the open questions in `docs/plans/2026-08-14-lean-sig-facade-design.md`: record the
measured `LEAF_TARGET`, the final crate name, and the `generate`-without-RNG decision (now
resolved — `generate` takes no RNG; `from_seed` covers deterministic testing).

Also record what is knowingly untested, so nobody later mistakes absence for coverage:
the **accepting** side of the 32768 ceiling (exactly 32768 signers passes the check and goes
on to prove 22 leaves — untestable at any tier), `MAX_XMSS_DUPLICATES` (reachable only after
proving everything below the root, since an exact pre-check means simulating the tree), and
whether the bottom-subtree cache actually saves work (a timing property, with no benchmark
harness here to assert it without inventing one).

**Done.** The design doc's "Open questions" is now a "Resolved questions" section, followed by
"Knowingly untested", an operational note on the runner's stdout diagnostic, and "Follow-up".
It also records one item this step did not anticipate: the **largest leaf that proves** is
still unmeasured, so `LEAF_TARGET = 1500` is known-good rather than known-optimal.

**Step 6: Commit**

```bash
git commit -am "docs: resolve lean_multisig_api design open questions"
```

---

## Tuning questions deferred from Task 3 to Task 6

The planner (`plan.rs`) is deliberately conservative. Three shape decisions were left
unmeasured rather than guessed at; all three are measurement work, not redesign.

**Wall-clock is the sum over nodes, not a critical path.** `crates/backend/zk-alloc/src/lib.rs:99`
asserts *"only one proving job runs at a time"*. So any reasoning of the form "the widest node
dominates" is wrong here — minimizing total node count is what matters. Greedy `chunks(16)` already
does that (`ceil(L/16)` is minimal). The genuine open question is whether per-node trace **padding**
makes a 16+1 split cost more than a balanced 9+8, which only measurement settles.

> **Task 8 measurement, bearing directly on this.** 1500 raw signatures is one node at
> `RATE_ROOT` and takes **8.16s**. 1501 is two leaves at `RATE_LEAF` under a root at
> `RATE_ROOT` — three proving jobs, one more signature — and takes **6.74s**. The 3-node plan
> is *cheaper*. Minimizing node count is therefore the wrong primary objective: the **rate**
> the planner assigns dominates the node count it creates, because only the root pays
> `RATE_ROOT`. This points against the intuition that motivated the paragraph above. Anyone
> picking this up should measure rate assignment first and node count second. (Both figures are
> from `round_trip.rs`'s two `#[ignore]`d boundary tests, which CI now runs.)

**Mixed raw+child nodes are unused but supported.** The planner never emits a node holding both
raw signatures and child proofs: `raw` is non-empty if and only if `children` is empty. But
`aggregate_single_message_signatures(children, raw_xmss, ...)` accepts both, and `src/main.rs:111-117`
— the same topology `LEAF_TARGET` is derived from — mixes at raw counts of 10 and 25.

The cost of not mixing falls on what is likely the most common call: for `n_raw <= LEAF_TARGET`
with 1..=15 supplied children ("add my batch of signatures to an existing aggregate"), the current
plan is **two** proving jobs — a leaf, then a root merging it with the passthroughs — where one node
holding both would be **one**. At minutes per job that is roughly 2x on the incremental path.

Before implementing it, measure whether `LEAF_TARGET` raw plus a full fan-in of children fits the
trace bound. `main.rs` only ever mixes at small raw counts, which is consistent with a conservative
rule that would itself need measuring. Getting this wrong means a failed proof after minutes of work.

**The degenerate leaf.** `step_by(LEAF_TARGET)` means `plan(LEAF_TARGET + 1, 0)` produces leaves of
1500 and **1** — a full proving job for a single signature. Same greedy-vs-balanced question as
above, with a more extreme worst case.

---

## Notes for the implementer

- **Do not** add multi-message aggregation. It was explicitly ruled out of scope.
- Task 6's entry point must call `plan(raw.len(), children.len())` itself and never accept an
  externally-constructed `Plan`. The plan's `Range`s and `Passthrough` indices point into
  caller-owned slices with nothing type-level tying them together, so constructing a plan away
  from its slices is the one way to misuse this module.
- **Do not** expose `log_inv_rate`, topology, or any `rec_aggregation` type in a public
  signature. The entire point is that callers have no knobs.
- `LEAF_TARGET = 1500` is inherited from a tuned benchmark topology, not derived. If a leaf
  ever exceeds the table-height limit, lower it and say so in the design doc.
- Prefer widening a test's signer count over deleting a test if the prover misbehaves at small
  sizes. A recently fixed bug (`cea9fe7`) lived exactly in that small-instance regime.
