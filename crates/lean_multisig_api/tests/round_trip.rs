//! The only tests that run a real aggregation.
//!
//! Everything else in this crate's suite stops at an early return, a pure function, or a
//! hand-built fixture; these produce genuine proofs and feed them back through the public API.
//! That makes them the sole home of several claims the cheaper tiers cannot even phrase — the
//! mixed raw+aggregate input path, the passthrough of a *valid* aggregate, and the discrimination
//! between `MalformedSignature` and `MalformedEntry` — each marked below.
//!
//! # Cost
//!
//! Proving is the entire runtime, so this file spends it deliberately: one 2-signer aggregate is
//! built once and shared by every test that only needs *some* valid aggregate. Two signers is as
//! structurally meaningful as two hundred for everything asserted here, and proportionally
//! cheaper. Seven of the twelve default tests run no proving job at all — four never call
//! `aggregate`, and three more are rejected before the planner or planned as a passthrough — so
//! the binary's ten-odd seconds belongs to the other five, most of it to
//! `a_multi_level_tree_round_trips`.
//!
//! Release, in practice: measured at 10-12s with `--release` against 317s without, on the same
//! machine. Both pass, so an unoptimized run is a patience problem rather than a broken one. CI
//! runs `cargo test --release --all` (`.github/workflows/rust.yml`), so release is the figure CI
//! pays and debug is what a local `cargo test` costs.
//!
//! # Why the two boundary tests are `#[ignore]`d
//!
//! `a_leaf_target_sized_batch_proves` and `a_batch_one_past_leaf_target_splits_and_proves` prove
//! real 1500- and 1501-signature batches, to check that `plan::LEAF_TARGET` is a leaf size the
//! prover accepts rather than a number inherited from a benchmark topology. They are the only
//! tests here whose *size* is the point rather than an incidental cost.
//!
//! Not gated because they are expensive in CI, which they are not. ~12s of proving in a job that
//! already spends minutes on a release build, and the 10,000-signer cache they load is already
//! paid for: `tests/test_multisignatures.rs` calls `get_benchmark_signatures` from tests that are
//! *not* ignored, so every CI run generates or loads it before this file is reached. The marginal
//! cost is the proving alone.
//!
//! **CI runs them.** `.github/workflows/rust.yml` has an `Ignored slow tests` step immediately
//! after `Test`, in the same job so it inherits the matrix condition and `SIGNERS_CACHE_DIR`. It
//! names this binary explicitly rather than passing `--include-ignored`, which would also run six
//! unrelated ignored tests elsewhere in the workspace, several of them benchmarks. So `#[ignore]`
//! here means "not in a local `cargo test`", not "unverified".
//!
//! They stay gated to keep *local* iteration bearable, where the debug suite already costs 317s
//! without them. Run them by hand after touching the planner:
//!
//! ```text
//! cargo test --release -p lean_multisig_api --test round_trip -- --ignored
//! ```
//!
//! No test here calls [`lean_multisig_api::warm_up`]: the lazy initialization inside each entry point is
//! what the whole file leans on, and `tests/lazy_init_*.rs` is where that is pinned per entry
//! point in a process each owns.

use lean_multisig_api::{Error, SecretKey, aggregate, verify, verify_with_signers};
use std::collections::BTreeSet;
use std::sync::{Mutex, MutexGuard, OnceLock};

const MSG: [u8; 32] = [42u8; 32];
const SLOT: u32 = 100;

/// Serializes proving across the test binary's threads.
///
/// Not currently load-bearing: `zk_alloc`'s phase assertion — the one that panics when two
/// proving jobs overlap — is a no-op until `enable_arena`, which only `lean-multisig`'s
/// `setup_prover` calls, and nothing in `lean_multisig_api`'s dependency path does. So concurrent
/// `aggregate` calls would today run rather than panic. They would still be two provers fighting
/// over the machine, and the day `lean_multisig_api` (or anything under it) engages the arena the failure
/// mode is a panic in whichever test loses the race. Following `tests/test_multisignatures.rs`'s
/// `ARENA_TEST_LOCK` precedent costs nothing and removes the question.
static PROVE_LOCK: Mutex<()> = Mutex::new(());

/// The shared 2-signer aggregate over `(MSG, SLOT)`, proved at most once per process.
///
/// Tests are independent in what they *assert* — this is a fixture, not a channel between them —
/// but sharing it means one proving job instead of six.
static BASE: OnceLock<Vec<u8>> = OnceLock::new();

/// `n` distinct keys, seeded `0..n`, each active over `SLOT`.
///
/// One-off keys elsewhere in this file are seeded from 200 up, deliberately disjoint from these.
/// XMSS is stateful: signing two *different* messages at one slot with one key leaks that slot's
/// WOTS key, and this file signs a second message in
/// `a_lone_aggregate_over_another_message_or_slot_is_rejected`. Nothing here would fail if the
/// seeds collided — the proofs would still verify — which is exactly why the separation has to be
/// deliberate rather than noticed later by a reader copying the pattern.
fn signers(n: u8) -> Vec<SecretKey> {
    (0..n)
        .map(|i| SecretKey::from_seed([i; 32], 100..=115).unwrap())
        .collect()
}

/// A key belonging to no `signers` set. See that function for why the ranges are kept apart.
fn lone_key(seed: u8) -> SecretKey {
    assert!(seed >= 200, "one-off seeds live at 200 and up");
    SecretKey::from_seed([seed; 32], 100..=115).unwrap()
}

/// Runs one aggregation with the prover to itself.
///
/// The lock is taken and released entirely inside this function. Nothing else acquires it, so no
/// caller can be holding it when it blocks on `BASE`'s initialization — which is exactly the
/// cycle that would deadlock, since `base` proves while holding the `OnceLock`.
fn prove(entries: Vec<Vec<u8>>, pubkeys: Vec<Vec<u8>>, message: [u8; 32], slot: u32) -> Result<Vec<u8>, Error> {
    let _guard: MutexGuard<'_, ()> = PROVE_LOCK.lock().unwrap();
    aggregate(entries, pubkeys, message, slot)
}

/// The two public keys `base` proves, in the caller's order (aggregation sorts them; compare as
/// sets).
fn base_pubkeys() -> Vec<Vec<u8>> {
    signers(2).iter().map(SecretKey::public_key).collect()
}

/// [`base_pubkeys`] as a set, which is how every comparison against a proved signer set wants
/// it — `proved_set` is the other half of the same pairing.
fn base_set() -> BTreeSet<Vec<u8>> {
    base_pubkeys().into_iter().collect()
}

/// A real aggregate over `(MSG, SLOT)` signed by `base_pubkeys()`.
fn base() -> &'static [u8] {
    BASE.get_or_init(|| {
        let keys = signers(2);
        let sigs: Vec<_> = keys.iter().map(|k| k.sign(&MSG, SLOT).unwrap()).collect();
        let pks: Vec<_> = keys.iter().map(SecretKey::public_key).collect();
        prove(sigs, pks, MSG, SLOT).expect("aggregating two honest signatures must succeed")
    })
}

/// The proved signer set as a set, since `verify` returns the library's canonical sorted order
/// rather than the order anything was aggregated in.
fn proved_set(aggregate_bytes: &[u8]) -> BTreeSet<Vec<u8>> {
    verify(aggregate_bytes, &MSG, SLOT).unwrap().into_iter().collect()
}

#[test]
fn aggregate_then_verify_returns_the_signer_set() {
    // The end-to-end claim the whole crate exists to make: keys sign, `aggregate` proves, and
    // `verify` reports exactly who signed. Everything below is a variation on this failing.
    let pks = base_pubkeys();
    let agg = base();

    assert_eq!(proved_set(agg), pks.iter().cloned().collect::<BTreeSet<_>>());

    // The same claim through the API that checks the set for you.
    verify_with_signers(agg, &pks, &MSG, SLOT).unwrap();
}

#[test]
fn verify_rejects_the_wrong_message_and_slot() {
    // The proof is valid; it just does not prove what is being asked about. This is the check
    // that binds an aggregate to a `(message, slot)` — `verify_single_message_aggregate` on its
    // own validates the aggregate against its *own* pair and would happily pass.
    let agg = base();
    assert!(matches!(verify(agg, &[0u8; 32], SLOT), Err(Error::MessageMismatch)));
    assert!(matches!(verify(agg, &MSG, SLOT + 1), Err(Error::MessageMismatch)));
    assert!(matches!(
        verify_with_signers(agg, &base_pubkeys(), &[0u8; 32], SLOT),
        Err(Error::MessageMismatch)
    ));
}

#[test]
fn verify_rejects_a_tampered_proof() {
    // A real proof with one byte changed, in the two classes that turn out to exist. Which class
    // a mutation falls into is decided by postcard, not by the prover: field elements are LEB128
    // varints, so most edits move a continuation bit and desynchronize every value after it.
    //
    // Measured by hand over 64 evenly spaced offsets — that probe is not committed; the sweep at
    // the end of this test is a different, smaller one of 15 offsets and 30 mutations. `^= 0xff`
    // gives `MalformedAggregate` at 63 of the 64 and never reaches the proof check (the odd one
    // out is byte 0, the message's first byte, which gives `MessageMismatch`). `^= 0x01` gives
    // `Error::Proof` at all 63 and `MalformedAggregate` at none. Neither mask is ever accepted at
    // any offset.
    //
    // Even spacing tops out at `len * 63/64`, so the probe never lands on the last byte — which
    // is precisely the byte the class-1 assertion below flips. That assertion is its own evidence;
    // the sweep above it is not.
    let agg = base();

    // Class 1: framing broken, so the blob stops being an aggregate before any proof work.
    let mut framing = agg.to_vec();
    *framing.last_mut().unwrap() ^= 0xff;
    let result = verify(&framing, &MSG, SLOT);
    assert!(
        matches!(result, Err(Error::MalformedAggregate)),
        "a wholesale byte flip breaks postcard framing, got {result:?}"
    );

    // Class 2: the interesting one. Flipping the *low* bit preserves every varint's length and
    // leaves the field element canonical, so the aggregate parses and the proof itself is what
    // rejects it. This is the only place a genuine `Error::Proof` comes out of a real proof —
    // `tests/unprovable_child.rs` reaches that variant with a hand-built empty transcript, which
    // says nothing about what a prover actually emits.
    let mut tampered = agg.to_vec();
    tampered[agg.len() / 2] ^= 0x01;
    let result = verify(&tampered, &MSG, SLOT);
    assert!(
        matches!(result, Err(Error::Proof(_))),
        "a framing-preserving edit must reach the proof check, got {result:?}"
    );

    // The claim both classes serve: no single-byte change anywhere is *accepted*. Verify-only, so
    // this sweep is milliseconds. If the encoding ever drifts and class 2 stops reaching the proof
    // check, this still holds and the assertion above is what fails — which is the right place to
    // find out.
    for k in 1..16 {
        let offset = agg.len() * k / 16;
        for mask in [0x01u8, 0xff] {
            let mut bytes = agg.to_vec();
            bytes[offset] ^= mask;
            let result = verify(&bytes, &MSG, SLOT);
            assert!(
                result.is_err(),
                "flipping {mask:#04x} at byte {offset} verified: {result:?}"
            );
        }
    }
}

#[test]
fn verify_rejects_a_different_expected_signer_set() {
    // `verify_with_signers` exists so a caller cannot forget to check *who* signed; a set that
    // is merely plausible must fail as loudly as garbage.
    let agg = base();
    let pks = base_pubkeys();
    let outsider = lone_key(200).public_key();

    // One real signer swapped for someone who never signed.
    assert!(matches!(
        verify_with_signers(agg, &[pks[0].clone(), outsider.clone()], &MSG, SLOT),
        Err(Error::SignerSetMismatch)
    ));
    // A subset fails too: a signer missing from `expected` is as wrong as an extra one.
    assert!(matches!(
        verify_with_signers(agg, &[pks[0].clone()], &MSG, SLOT),
        Err(Error::SignerSetMismatch)
    ));
    // And a superset, which is the shape a caller checking "did my validators sign?" gets wrong.
    let superset = [pks[0].clone(), pks[1].clone(), outsider];
    assert!(matches!(
        verify_with_signers(agg, &superset, &MSG, SLOT),
        Err(Error::SignerSetMismatch)
    ));
    // Repeats in `expected` are ignored, as documented — this is the *passing* side.
    verify_with_signers(agg, &[pks[0].clone(), pks[1].clone(), pks[0].clone()], &MSG, SLOT).unwrap();
}

#[test]
fn folding_an_aggregate_with_fresh_signatures_unions_the_signers() {
    // The mixed-input path, and the only test anywhere that sees `codec::classify` return
    // successfully with its `aggregates` vector non-empty. Unit tests cannot reach it: parsing a
    // real aggregate needs the bytecode `OnceLock` filled and a genuine `ExecutionProof`.
    //
    // Also the shape where the two input vectors are deliberately *not* index-aligned:
    // `proof_or_sig` holds an aggregate and one raw signature, and `public_keys` holds exactly
    // one key — the raw one's. A caller who assumed alignment would pass two keys and get
    // `PubkeyCountMismatch`.
    //
    // The assertion is the *union*, not merely `Ok`: pairing the third signature with the wrong
    // key, or dropping the child's signers, both produce a perfectly valid proof of the wrong
    // signer set, which no `is_ok` check would notice.
    let fresh = lone_key(201);
    let outer = prove(
        vec![base().to_vec(), fresh.sign(&MSG, SLOT).unwrap()],
        vec![fresh.public_key()],
        MSG,
        SLOT,
    )
    .unwrap();

    let mut expected = base_set();
    expected.insert(fresh.public_key());
    assert_eq!(expected.len(), 3, "the fresh signer must be a genuinely new key");
    assert_eq!(proved_set(&outer), expected);
    verify_with_signers(&outer, &expected.iter().cloned().collect::<Vec<_>>(), &MSG, SLOT).unwrap();
}

#[test]
fn duplicate_raw_signatures_collapse_to_one_signer() {
    // `dedup_signers` is pinned as a pure function in the unit suite, which is where its
    // "earliest signature wins" tie-break belongs. What that cannot show is that the deduplicated
    // batch is still something the prover accepts, and that the *proved* set is the deduplicated
    // one rather than a set with a repeat in it — a repeat that upstream would later charge
    // against `MAX_XMSS_DUPLICATES`.
    let keys = signers(2);
    let (a, b) = (&keys[0], &keys[1]);
    // The same key offered twice, beside a second key that must survive untouched. Signing the
    // same (message, slot) twice is derandomized and byte-identical, so this is the innocent
    // shape a caller hits by merging two overlapping gossip batches.
    let entries = vec![
        a.sign(&MSG, SLOT).unwrap(),
        a.sign(&MSG, SLOT).unwrap(),
        b.sign(&MSG, SLOT).unwrap(),
    ];
    let pks = vec![a.public_key(), a.public_key(), b.public_key()];

    let agg = prove(entries, pks, MSG, SLOT).unwrap();
    assert_eq!(
        proved_set(&agg),
        base_set(),
        "a repeated signer must prove exactly once, and must not take the other one down with it"
    );
}

#[test]
fn a_signer_present_in_both_a_child_and_a_raw_batch_appears_once() {
    // The overlap `aggregate`'s rustdoc documents: the result's signer set is the *union* of the
    // raw pubkeys and every child's. `dedup_signers` cannot help here — it only sees the raw
    // vector — so this is upstream's per-node deduplication being relied on across the boundary
    // between a supplied aggregate and fresh signatures.
    //
    // Distinct from the excluded `MAX_XMSS_DUPLICATES` ceiling: this asserts that one overlapping
    // signer is *correct*, not how many the node tolerates before refusing.
    let keys = signers(2);
    let fresh = lone_key(204);
    let entries = vec![
        base().to_vec(),
        keys[0].sign(&MSG, SLOT).unwrap(), // already inside `base`
        fresh.sign(&MSG, SLOT).unwrap(),   // genuinely new
    ];
    let pks = vec![keys[0].public_key(), fresh.public_key()];

    let agg = prove(entries, pks, MSG, SLOT).unwrap();

    let mut expected = base_set();
    expected.insert(fresh.public_key());
    assert_eq!(expected.len(), 3, "two from the child plus one new one");
    assert_eq!(
        proved_set(&agg),
        expected,
        "the overlapping signer must appear once, and the new one must appear at all"
    );
}

#[test]
fn a_corrupt_signature_sized_blob_is_a_malformed_signature_not_a_malformed_entry() {
    // `codec`'s unit test of the same shape cannot discriminate what its name says: with no
    // bytecode initialized, a fall-through to the aggregate parser also returns `None`, so a
    // classifier that tried both would produce an error there too — just a different variant
    // nobody could distinguish from the right one.
    //
    // Here `aggregate` initializes the bytecode before `classify` runs, so the aggregate parser
    // is genuinely live: a fall-through would report `MalformedEntry`, and this asserts it does
    // not. The two variants have different remedies — damaged data versus data of the wrong kind
    // — which is why they are kept apart at all.
    let key = lone_key(202);
    let mut sig = key.sign(&MSG, SLOT).unwrap();
    assert_eq!(sig.len(), xmss::SIGNATURE_SSZ_LEN, "the classifier dispatches on this");
    sig[..4].copy_from_slice(&[0xff; 4]); // non-canonical field element

    // No proving: this fails inside `classify`, before the planner.
    let result = prove(vec![sig], vec![key.public_key()], MSG, SLOT);
    assert!(
        matches!(result, Err(Error::MalformedSignature { index: 0 })),
        "a 1208-byte blob must never fall through to the aggregate parser, got {result:?}"
    );
}

#[test]
fn a_signature_paired_with_the_wrong_key_fails_in_the_prover() {
    // The mistake this API's shape invites: the right *number* of pubkeys in the wrong order.
    // Nothing before proving can catch it — the counts match and both blobs decode — so the
    // constraint system is what rejects it, as `Error::Aggregation(Prover(Runner(..)))`.
    //
    // Pinned because the alternative to an error here is a *panic*: this is a public entry point
    // fed by gossip, and a constraint failure on attacker-supplied bytes must stay a `Result`.
    // Nothing else in the suite reaches the runner's failure path, so a change to how it reports
    // unsatisfied constraints could turn this into an abort with every other test still green.
    //
    // The diagnostic is a bare constraint mismatch carrying no index and no hint that pubkey
    // ordering is the thing to check — see `aggregate`'s `# Errors`, which now says so.
    let a = lone_key(205);
    let b = lone_key(206);
    let result = prove(vec![a.sign(&MSG, SLOT).unwrap()], vec![b.public_key()], MSG, SLOT);
    assert!(matches!(result, Err(Error::Aggregation(_))), "got {result:?}");
}

#[test]
fn a_lone_valid_aggregate_is_passed_through_unchanged() {
    // `plan(0, 1)` is `Passthrough`, the one shape where `aggregate` proves nothing and hands
    // back what it was given. Cheap, and therefore the shape most likely to quietly return the
    // wrong thing: it is the only path where no node re-derives the signer set, and the only one
    // where no node verifies the child's proof either (`aggregate` does that itself at the root
    // — `tests/unprovable_child.rs` is the negative side of that check; this is the positive one,
    // which is what shows the check does not reject *valid* aggregates too).
    let out = prove(vec![base().to_vec()], vec![], MSG, SLOT).unwrap();

    assert_eq!(proved_set(&out), base_set(), "a passthrough must not change who signed");
    // Decode/re-encode is the identity, so the passthrough is a passthrough in bytes and not
    // merely in meaning. `rebuild_bytecode_claim` recomputes the claim's value on the way in and
    // `to_bytes` never writes it, so the round trip has nothing to drift on.
    assert_eq!(
        out,
        base(),
        "re-encoding a lone aggregate must reproduce it byte for byte"
    );
}

#[test]
fn a_multi_level_tree_round_trips() {
    // The planner's fold loop and `execute`'s nested recursion, on real proofs. Every other test
    // here plans a single node or a root over two children, so the `while pool.len() > MAX_FAN_IN`
    // branch runs nowhere else — and with it the only `Passthrough` under a *non-root* node,
    // which is what makes `execute` recurse into a child that is itself a folded internal node.
    // (`Passthrough` under the root is not unique to this test:
    // `folding_an_aggregate_with_fresh_signatures_unions_the_signers` plans `Node { children:
    // [leaf, Passthrough(0)] }` and so also takes the `Cow::into_owned` clone.)
    //
    // Depth comes from the fan-in, not from `LEAF_TARGET`: 1501 raw signatures would split into
    // two leaves, but 17 supplied children fold into an internal node over 16 plus a leftover,
    // which is a three-level tree. Reaching it through raw signatures alone would need 1500 * 17
    // of them, which is not a test at any budget.
    //
    // The plan for this crate expected it to be `#[ignore]`d as unaffordably slow. Measured, it
    // is 19 proving jobs in ~8s — the whole of the rest of this file is ~4s — so it runs in CI
    // like everything else. It is still by far the most expensive test here, and the first place
    // to look if this binary's runtime ever becomes a problem.
    let keys = signers(17);
    let children: Vec<Vec<u8>> = keys
        .iter()
        .map(|k| prove(vec![k.sign(&MSG, SLOT).unwrap()], vec![k.public_key()], MSG, SLOT).unwrap())
        .collect();

    let root = prove(children, vec![], MSG, SLOT).unwrap();

    let expected: BTreeSet<Vec<u8>> = keys.iter().map(SecretKey::public_key).collect();
    assert_eq!(expected.len(), 17, "every child must contribute a distinct signer");
    assert_eq!(proved_set(&root), expected);
}

#[test]
fn a_lone_aggregate_over_another_message_or_slot_is_rejected() {
    // The check that has to live in `aggregate` itself. Upstream compares a child's `(message,
    // slot)` only at the node that *consumes* it, and a lone aggregate is consumed by nothing —
    // so without this, `aggregate` returns an aggregate over MSG as a success for a caller who
    // asked for a different message entirely, and the caller then gossips it as proof of the
    // wrong thing.
    let other = [7u8; 32];
    assert_ne!(other, MSG);
    let result = prove(vec![base().to_vec()], vec![], other, SLOT);
    assert!(matches!(result, Err(Error::MessageMismatch)), "got {result:?}");

    let result = prove(vec![base().to_vec()], vec![], MSG, SLOT + 1);
    assert!(matches!(result, Err(Error::MessageMismatch)), "got {result:?}");

    // The same fault with a sibling present, which is the shape upstream would eventually catch
    // on its own — but only after proving the sibling's leaf. Fails here in milliseconds instead.
    let fresh = lone_key(203);
    let result = prove(
        vec![base().to_vec(), fresh.sign(&other, SLOT).unwrap()],
        vec![fresh.public_key()],
        other,
        SLOT,
    );
    assert!(matches!(result, Err(Error::MessageMismatch)), "got {result:?}");
}

/// Mirror of `plan::LEAF_TARGET`, which is `pub(crate)` in a private module and so invisible
/// here. Nothing enforces that these agree — if the constant moves, the tests below quietly stop
/// testing the boundary they are named for, which is the cost of not exposing it.
const LEAF_TARGET: usize = 1500;

/// The first `n` pre-generated benchmark signatures, as `(entries, pubkeys)` in `aggregate`'s
/// argument shapes.
///
/// Real keygen for 1501 signers would dwarf the proving these tests exist to measure;
/// `xmss::signers_cache` generates 10,000 once and caches them on disk (`target/signers-cache`,
/// or `$SIGNERS_CACHE_DIR`), which is the same cache `tests/test_multisignatures.rs` uses. They
/// are signed over `message_for_benchmark()` at `BENCHMARK_SLOT`, not this file's `MSG`/`SLOT`.
fn benchmark_batch(n: usize) -> (Vec<Vec<u8>>, Vec<Vec<u8>>) {
    use ssz::Encode;
    let signatures = xmss::signers_cache::get_benchmark_signatures();
    assert!(signatures.len() >= n, "the cache holds {} signatures", signatures.len());
    signatures[..n]
        .iter()
        .map(|(pk, sig)| (sig.as_ssz_bytes(), pk.as_ssz_bytes()))
        .unzip()
}

#[test]
#[ignore = "slow: proves a full 1500-signature leaf"]
fn a_leaf_target_sized_batch_proves() {
    // The crate's biggest untested assumption. `plan::LEAF_TARGET` is 1500 because `src/main.rs`'s
    // tuned topology proves leaves of 508..1550 — it was inherited, not computed against the 2^22
    // table height. If a 1500-signature node does not actually prove, every aggregation past that
    // many signers fails at runtime, and nothing in the default suite would notice: its largest
    // single node holds three signatures.
    //
    // `plan(LEAF_TARGET, 0)` is one node at `RATE_ROOT`, which is also the slowest rate the
    // planner uses — so this is the worst case for the boundary, not a favourable reading of it.
    //
    // Measured: it proves, in ~8s release including the cache load. So 1500 is a real leaf size
    // and not merely an inherited one. That is a statement about this one shape at this one rate;
    // the largest leaf that proves is still unmeasured, and the constant sits below 1550 for
    // reasons `plan.rs` records rather than reasons anything checks.
    let message = xmss::signers_cache::message_for_benchmark();
    let slot = xmss::signers_cache::BENCHMARK_SLOT;
    let (entries, pubkeys) = benchmark_batch(LEAF_TARGET);

    let agg = prove(entries, pubkeys, message, slot).expect("a LEAF_TARGET-sized leaf must prove");
    assert_eq!(
        verify(&agg, &message, slot).unwrap().len(),
        LEAF_TARGET,
        "every signer must survive to the wire proof"
    );
}

#[test]
#[ignore = "slow: proves two leaves and a root over 1501 signatures"]
fn a_batch_one_past_leaf_target_splits_and_proves() {
    // One signature past the boundary, which is where `plan` stops returning a single node and
    // starts returning `[leaf(0..1500), leaf(1500..1501)]` under a root — three proving jobs, and
    // the degenerate one-signature leaf the planner's own test records as a shape it tolerates.
    // Neither the split nor that leaf has ever been proved for real.
    //
    // Measured at ~7s against the single 1500-node's ~8s — one more signature, three proving jobs
    // instead of one, and *less* wall-clock, because the two leaves run at `RATE_LEAF` and only
    // the root pays `RATE_ROOT`. Worth knowing before optimizing node counts: the rate the
    // planner assigns dominates how many nodes it creates.
    let message = xmss::signers_cache::message_for_benchmark();
    let slot = xmss::signers_cache::BENCHMARK_SLOT;
    let (entries, pubkeys) = benchmark_batch(LEAF_TARGET + 1);

    let agg = prove(entries, pubkeys, message, slot).expect("a split batch must prove");
    assert_eq!(verify(&agg, &message, slot).unwrap().len(), LEAF_TARGET + 1);
}
