# `lean_multisig_api`: an opinionated facade over XMSS and aggregation

**Status:** implemented (Tasks 1-8 complete)
**Date:** 2026-08-14

> **Crate renamed.** This file is named `2026-08-14-lean-sig-*` and the commits from Tasks 1-7
> are scoped `feat(lean_sig)` / `test(lean_sig)`, because `lean_sig` was the working name until
> Task 8 renamed the crate to **`lean_multisig_api`**. The filename and those commit scopes are
> left alone deliberately: they are how existing commit messages refer to this work. Everything
> else here says `lean_multisig_api`.

## Purpose

`xmss` and `rec_aggregation` expose the full parameter space: `log_inv_rate`, recursion
topology, bytecode claims, field elements. Callers who just want to sign and aggregate must
first learn which of those choices matter.

`lean_multisig_api` removes the choices. It exposes signing and single-message aggregation over
byte slices, and picks every tuning parameter internally. Callers who need the full
parameter space keep using `rec_aggregation` directly; this crate does not try to replace it.

## Scope

In scope:

- XMSS keygen, signing, verification.
- Single-message aggregation: one `(message, slot)` shared by every signer.
- Verification of such an aggregate.

Out of scope:

- Multi-message aggregation (`merge_single_message_aggregates`,
  `split_multi_message_aggregate`). Callers needing cross-message merging use
  `rec_aggregation`.
- Any control over `log_inv_rate` or recursion topology.

## Public surface

Everything crossing the boundary is either a `Vec<u8>` wire format or an opaque handle.
No `KoalaBear`, `Evaluation<EF>`, or `MultilinearPoint` appears in a signature.

### Handles

State expensive enough to hold across operations gets a real type.

```rust
pub struct SecretKey(xmss::XmssSecretKey);

impl SecretKey {
    // As built: one inclusive slot range, not the (activation_slot, num_active_slots) pair
    // upstream takes. The range round-trips through `slots()`, and an empty one is an error.
    pub fn generate(slots: RangeInclusive<u32>) -> Result<Self, Error>;
    pub fn from_seed(seed: [u8; 32], slots: RangeInclusive<u32>) -> Result<Self, Error>;
    pub fn from_bytes(b: &[u8]) -> Result<Self, Error>;
    pub fn to_bytes(&self) -> Vec<u8>;

    pub fn public_key(&self) -> Vec<u8>;                 // PUB_KEY_SSZ_LEN = 32
    pub const fn slots(&self) -> RangeInclusive<u32>;
    pub fn prepare(&self, slot: u32) -> Result<(), Error>;
    pub fn sign(&self, message: &[u8; 32], slot: u32) -> Result<Vec<u8>, Error>;
                                                          // SIGNATURE_SSZ_LEN = 1208
}
```

`XmssSecretKey` holds a `top: Vec<Vec<Digest>>` tree and a `Mutex<Option<BottomSubtree>>`
cache warmed by `prepare`. Serialization persists the seed, slot range, and top tree, but
drops the cache. A pure `sign(sk_bytes, msg, slot)` function would therefore rebuild a
bottom subtree on every call. The handle keeps the cache warm across signatures.

`prepare` survives into the facade. It is the one piece of tuning the library cannot infer,
because only the caller knows which slot is coming next.

`sign` returns SSZ bytes rather than a handle so its output drops straight into
`aggregate`'s first argument.

### Bytes

Public keys, signatures, and aggregates are inert blobs. They get no newtype; wrapping them
would buy nothing but conversions.

### Aggregation

```rust
pub fn aggregate(
    proof_or_sig: Vec<Vec<u8>>,
    public_keys: Vec<Vec<u8>>,
    message: [u8; 32],
    slot: u32,
) -> Result<Vec<u8>, Error>;

#[must_use]
pub fn verify(
    aggregate: &[u8],
    message: &[u8; 32],
    slot: u32,
) -> Result<Vec<Vec<u8>>, Error>;   // Ok holds the signer set actually proved

pub fn verify_with_signers(
    aggregate: &[u8],
    expected: &[Vec<u8>],
    message: &[u8; 32],
    slot: u32,
) -> Result<(), Error>;

pub fn warm_up();
```

## Dispatch and pubkey pairing

`proof_or_sig` mixes raw XMSS signatures and previously produced aggregates. Entries are
classified by length: exactly `SIGNATURE_SSZ_LEN` (1208) means a raw signature; any other
length is parsed as a postcard aggregate via `SingleMessageAggregateSignature::from_bytes`.

A 1208-byte blob that fails SSZ decode is an error, never a fallback to the aggregate parse.
Silent reclassification would surface as a baffling failure much later.

Aggregates carry their own signer sets (`info.pubkeys`), so `public_keys` covers raw
signatures only: the *k*-th raw entry, in order, pairs with `public_keys[k]`. When the counts
disagree, `Error::PubkeyCountMismatch { expected, got }`. The two vectors are deliberately
not index-aligned, which is the main thing to document loudly.

## Tree planning

`aggregate` builds the whole recursion tree in one call and chooses `log_inv_rate` per level.
Lower rate means faster proving and a bigger proof; the useful range is 1 to 4.

- Raw signatures partition into leaves of `LEAF_TARGET` (1500), proved at rate 1. Leaf proofs
  are consumed immediately, so their size does not matter.
- Supplied child aggregates enter at the level above, fanning in at most `MAX_RECURSIONS`
  (16) per node, at rate 2.
- The root is proved at rate 4. It is what goes on the wire, so it gets the smallest proof.
- Special case: when everything fits in one node it is proved at rate 4 directly, because that
  node *is* the wire proof. Proving it at rate 1 would hand the caller a needlessly large one.
- A leftover group of one is passed through rather than wrapped in a single-child node, which
  would prove its only child a second time for nothing.

`LEAF_TARGET` was taken from the hand-tuned topology in `src/main.rs`, whose leaves hold 508
to 1550 raw signatures. An earlier draft of this document said it was "tuned against the 2^22
table-height limit" — it was not; no such calculation was ever done, and that clause overclaimed
rigor the number did not have. It has since been *measured* instead: see Resolved questions.

### Capacity

`aggregate_single_message_signatures` computes `global_pub_keys` as the sorted, deduplicated
union of raw pubkeys and every child's pubkeys, and rejects it above `MAX_XMSS_AGGREGATED`
(2^15 = 32768). That check applies at every node including the root, so **recursion does not
extend signer capacity**: 32768 distinct signers is the ceiling for the entire tree. The tree
exists to get past the roughly 1500 signatures a single node can prove, not past 32768.

The facade checks this ceiling up front, before proving anything, and returns
`Error::TooManySigners { got, max }`. Failing after minutes of proving would be needlessly
cruel.

### Sequential cost

A whole-tree call is strictly sequential: `execute` proves nodes one after another, so
wall-clock is the sum of every node's proving time with no intra-call parallelism. That much
is unconditional, and it is documented on `aggregate` itself.

The *cross-call* claim needs more care than this document originally gave it. It said
concurrent calls panic, citing `rec_aggregation`. That is only conditionally true.
`zk_alloc::begin_phase` returns early unless `enable_arena` has run, and `enable_arena` is
called in exactly one place — `lean_multisig::setup_prover`. An application on
`setup_prover_without_arena` never engages it either. So two concurrent `aggregate` calls
panic under an embedder that called `setup_prover`, and quietly succeed in a
`lean_multisig_api`-only harness.

That asymmetry is a trap worth naming: a caller who tests concurrency in isolation sees it
work and concludes the warning is stale. Serialize `aggregate` calls unconditionally.

**Measured cost.** An earlier draft of this document said "minutes per node", which was wrong
by about two orders of magnitude at the sizes anyone tests. Release measurements: 19 small
nodes in ~8s; one full 1500-signature leaf in ~8s; a 2-signer aggregate plus verify in ~3s.
The framing had propagated to seven doc sites in the crate and was corrected in all of them.

## Initialization

`get_aggregation_bytecode()` panics with `"call init_aggregation_bytecode() first"`, and
`SingleMessageAggregateSignature::from_bytes` silently returns `None` when the `OnceLock` is
unset.

Every public entry point calls `init_aggregation_bytecode()` first. It is a `OnceLock`, so
this is idempotent and free after the first call, and both sharp edges disappear. The caller
never learns the bytecode exists.

The first `aggregate` or `verify` in a process absorbs the one-time compile. `warm_up()` lets
long-running services pay that at startup instead.

## Why `verify` returns the signer set

An aggregate over the wrong validator set is still a perfectly valid proof. A `bool` return
invites `if verify(..) { .. }` while the caller forgets to check *who* signed.

An earlier draft of this document claimed returning the signer set means the API "cannot be
used without confronting it". That overclaims, and it is worth correcting precisely because it
is the kind of sentence a security reviewer leans on: `verify(..)?;` compiles silently, since
after `?` the type is a plain `Vec<Vec<u8>>` with no `#[must_use]`. What the design actually
buys is that ignoring the signer set requires *discarding a value* rather than simply not
asking for one — a real improvement over `bool`, but not a guarantee the type system enforces.
`verify_with_signers` exists for the common case where the expected set is already known.

Because every input is bytes, deserialization always runs `rebuild_bytecode_claim`, which
recomputes the trusted `bytecode_claim.value`. The unsound path that `rec_aggregation` warns
about, a trusted claim taken from an untrusted source, is unreachable through this facade.

## Errors

One `#[non_exhaustive] pub enum Error` implementing `std::error::Error`, flattening
`XmssKeyGenError`, `XmssSignatureError`, `XmssVerifyError`, `AggregationError`, `ProofError`,
and the facade's own parse and pairing variants. No generics; no source-crate types leak.

## Layout

`crates/lean_multisig_api/src/`:

| File | Contents |
| --- | --- |
| `lib.rs` | Public surface only. No `pub mod`. |
| `key.rs` | `SecretKey` handle; SSZ codecs at the boundary. |
| `codec.rs` | Length dispatch, pubkey pairing. |
| `plan.rs` | Tree planner: `LEAF_TARGET`, fan-in, per-level rate. Pure. |
| `error.rs` | The flattened `Error` enum. |

As built: no workspace manifest edit was needed. The root `members` is `["crates/*", ...]`, so
creating the directory registers the crate. It is deliberately *not* in
`[workspace.dependencies]` — nothing in the workspace depends on it, and an entry there would
be dead weight until something does.

## Testing

The layers differ enormously in cost, so they are tested separately.

**Unit, no proving.** `plan.rs` is pure so the planner is testable without a prover: for 1,
500, 1550, and 32768 signatures, assert leaf count, fan-in at most 16, and rates descending
1 → 2 → 4 toward the root. For `codec.rs`: a 1208-byte blob classifies as raw, a malformed
one errors rather than reclassifying, and pairing arithmetic holds when aggregates are
interleaved among raw signatures.

**Integration, slow.** `crates/lean_multisig_api/tests/`, modelled on `tests/test_multisignatures.rs`,
with `parallel`'s `forbid-parallelism` and `xmss`'s `test-utils` as dev-dependencies. Round
trip: keygen, sign, `aggregate`, then `verify` returns exactly the input signer set. Keep
these to single-digit signers and one leaf so CI stays usable; gate a multi-level tree test
behind `#[ignore]`.

As built, the multi-level tree test is *not* gated. Tree depth comes from fan-in
(`MAX_FAN_IN = 16`), not from `LEAF_TARGET`, so 17 supplied children give a three-level tree —
19 proving jobs in ~8s release, which is affordable. The two tests that *are* gated are the
`LEAF_TARGET` boundary pair, and CI runs those in a scoped step; see
[Resolved questions](#resolved-questions).

**Negative tests.** Wrong message; wrong slot; tampered proof bytes; a signer set that
verifies as a proof but differs from the expected set; and `verify` called before any
`warm_up`, which must succeed through lazy init rather than panic.

## Resolved questions

All three questions this document opened with are now settled.

### `LEAF_TARGET` — measured, and it holds

1500 was inherited from `src/main.rs`'s tuned topology (leaves of 508..1550) rather than
computed against the 2^22 table height. It has now been proved for real, by two `#[ignore]`d
tests in `crates/lean_multisig_api/tests/round_trip.rs` that CI runs in a scoped step:

| Shape | Plan | Proving jobs | Wall-clock (release) | Verified signers |
| --- | --- | --- | --- | --- |
| 1500 raw signatures | one node at `RATE_ROOT` | 1 | 8.16s | 1500 |
| 1501 raw signatures | two leaves at `RATE_LEAF` under a root at `RATE_ROOT` | 3 | 6.74s | 1501 |

1500 is measured at `RATE_ROOT`, which is the *slowest* rate the planner ever assigns — so this
is the worst case for the boundary, not a favourable reading of it.

**The 3-node split is cheaper than the single node, despite proving one more signature.** The
two leaves run at `RATE_LEAF` and only the root pays `RATE_ROOT`. This is direct evidence
bearing on the greedy-vs-balanced tuning question deferred from Task 3 (see the implementation
plan's "Tuning questions" section), and it points *against* the intuition that motivated it:
that section reasons about minimizing node count, on the grounds that wall-clock is the sum
over nodes rather than a critical path. That reasoning is correct as far as it goes, but the
measurement says the rate the planner assigns dominates the node count it creates. A topology
change that removes a node while pushing work up to a higher rate can be a net loss. Anyone
tuning the planner should measure rate assignment first and node count second.

**Still unmeasured: the largest leaf that proves.** 1500 sits below `main.rs`'s observed 1550
for inherited reasons, not checked ones. Nothing here probes where the table-height limit
actually bites. So `LEAF_TARGET = 1500` is **known-good, not known-optimal**, and the headroom
above it is unknown. Raising it is a measurement task, not a guess; lowering it needs no
evidence beyond a failure.

### The crate name — `lean_multisig_api`

`lean_sig` was a placeholder. The crate was renamed in Task 8; the plan-doc filenames and the
Task 1-7 commit scopes still say `lean_sig`, deliberately (see the note at the top).

### `SecretKey::generate` takes no RNG

Settled as-is: it does not, and will not. `from_seed` covers deterministic testing completely —
it is the same key derivation with the entropy supplied by the caller — so an RNG parameter
would buy only the ability to inject a *non-default* CSPRNG, which is not a use case this
facade exists to serve. Threading an `R: CryptoRng` through a "no knobs" API is exactly the
kind of parameter the crate was built to remove.

`generate_is_randomized` (in `key.rs`) pins the other half: that `generate` genuinely differs
run to run, and is not `from_seed` with a constant hiding in it.

## Knowingly untested

Absence of a test here is not absence of risk. These are the gaps that are known and were
judged not worth closing, rather than gaps nobody noticed.

- **The accepting side of the 32768-signer ceiling.** Exactly `MAX_XMSS_AGGREGATED` signers
  *passes* the up-front check and proceeds to prove 22 leaves. That is untestable at any tier —
  the check is cheap but what follows it is not. The **rejecting** side is tested
  (`aggregate_rejects_more_signers_than_the_ceiling`, 32769 synthetic pubkeys, ~3s), which is
  the side that turns "fails after the whole tree is proved" into "fails in milliseconds".

- **`MAX_XMSS_DUPLICATES`.** Reachable only *after* everything below the root has been proved,
  because the duplicate count depends on which node merges which children — so an exact
  pre-check would mean simulating the tree. `dedup_signers` removes the case a caller can
  trigger directly (the same key offered twice in one call). Several *supplied aggregates* with
  heavily overlapping signer sets can still hit the ceiling late, after minutes of proving.

- **Whether the bottom-subtree cache actually saves work.** `SecretKey` is a handle rather than
  a bytes-in/bytes-out `sign` precisely so `XmssSecretKey`'s `Mutex<Option<BottomSubtree>>`
  survives across signatures. That the cache is *preserved* is structural; that it *pays* is a
  timing property, and there is no benchmark harness in this crate to assert it without
  inventing one.

- **The largest leaf that proves.** See `LEAF_TARGET` above.

## Operational note: the runner prints to stdout on a constraint failure

Not a `lean_multisig_api` defect, but it affects anyone embedding it. When a raw signature
fails to verify under the public key it was paired with — the shape a misordered `public_keys`
produces — the zkVM runner **prints a diagnostic to stdout** on its way to returning
`Err(Error::Aggregation(..))`. Observed shape:

```text
ERROR

  at xmss_aggregate.py:109 in xmss_verify

  106 │         )
  107 │         target_sum += pair_sum_ptr[0]
  108 │
  109 │     assert target_sum == TARGET_SUM
      │     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  110 │

CALL STACK

  → xmss_verify() at main.py:176
    main() at main.py:35
```

The frames are labelled with line numbers from the aggregation program's own source, which
will mean nothing to a reader of the embedding application's logs. The error is returned
normally and nothing panics — but a node that captures stdout will emit this block for **every
malformed gossip batch**, which is attacker-controllable volume. Redirect or filter it if that
matters.

## Follow-up

- **Move the wire-format fixture upstream.** `tests/unprovable_child.rs` hand-encodes
  `SingleMessageAggregateSignature`'s postcard layout, relying on a tuple of the right leaves
  being byte-identical to a struct whose fields are `pub(crate)` and unconstructable from
  outside. `the_fixture_really_does_get_past_the_envelope` keeps it from going silently vacuous,
  which is what makes the technique safe today — but the knowledge lives in the wrong crate. A
  `rec_aggregation` `test-utils` feature exposing a constructor for a structurally valid,
  unprovable aggregate would put it where a field reorder is a compile error rather than a
  downstream fixture that parses by luck. `xmss` already gates `signers_cache` this way, so the
  pattern exists. **Deferred:** it changes another crate's public surface, which is outside the
  scope of a facade that is meant to depend on `rec_aggregation` rather than reshape it. Do it
  when `rec_aggregation` is next opened for its own reasons.
