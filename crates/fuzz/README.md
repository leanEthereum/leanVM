# leanVM fuzzing

An adversarial fuzzer for the whole stack: the field and hash kernels, the zkDSL compiler, the VM, the prover and the three verifiers, the recursion guest and the public aggregation API. It plays a malicious prover and a malicious aggregator, not only a source of noise: it forges single protocol messages and keeps Fiat-Shamir consistent afterwards, edits the committed witness in coordinated ways, forges the guest's hints, and hands the guest children the Rust verifier rejects.

## Running a campaign

```bash
cargo leanvm-fuzz run --duration 24h                 # every target, forever without --duration
cargo leanvm-fuzz run --targets soundness,guest- --jobs 4 --out fuzz-out
cargo leanvm-fuzz report                             # what it found, worst first
fuzz/campaign.sh --duration 24h --libfuzzer-jobs 8   # plus coverage-guided libFuzzer on the cheap targets (bash 4+)
```

`run` is a supervisor: it starts `--jobs` worker processes (a quarter of the CPUs by default, since proofs use the thread pool), gives each one target for a time slice (`--slice`, 600 s), and rotates targets by power scheduling: each gets at least its share of worker time (`--weights target=3,...` to change the shares), and a target whose time keeps reaching new behaviour earns up to five times more, so a long campaign drifts toward the targets still discovering something. Each worker draws its own `LEANVM_NUM_THREADS` unless `--threads` is given, so proofs run at many thread counts. A worker that panics, aborts, overflows its stack, exceeds `--mem-limit-mb` or spends longer than its target's timeout on one case (`--timeout-scale` to stretch) is killed if needed, recorded as a finding against the exact case it announced, and replaced. Everything persists in `--out` (`fuzz-out` by default): stopping and restarting resumes with the same corpus and findings, under a new base seed (`--seed` to fix it).

`cargo leanvm-fuzz` builds with the `fuzz` profile: release speed with `debug_assert!` and integer-overflow checks on, since an overflow is a bug a fuzzer should see. `LEANVM_FUZZ_SELFTEST=1 cargo leanvm-fuzz run --targets selftest --duration 3m --mem-limit-mb 4096` checks on a new machine that every kind of failure is caught (each `selftest-*` target fails one way on purpose).

## Triage

```bash
cargo leanvm-fuzz report [--fail-on high]
cargo leanvm-fuzz repro <target> --input fuzz-out/findings/<severity>/<target>/<key>/case-<n>.bin
cargo leanvm-fuzz minimize <target> --input <case file>
cargo leanvm-fuzz replay [--findings-only | --corpus-only] [--fail-on medium]
cargo leanvm-fuzz guest-coverage [--all]
```

A finding is deduplicated by its key, which names the bug and nothing about the case (a panic's location, a verifier error, a mutated field), so a campaign reports each bug once with a hit count and up to eight inputs. `finding.txt` in its directory has the key, the first detail and the command that reproduces it. `repro` replays the case in one process with panics printed; `minimize` shrinks the input while the same key reproduces, running each attempt in a subprocess so crashes count.

Severities:

| severity | meaning |
| -------- | ------- |
| critical | something false is accepted: a forged proof or witness verifies, the guest accepts a forged hint or an invalid child |
| high     | something true is refused or computed wrong: an honest proof fails, a miscompile, two implementations disagree, a proof depends on the thread count |
| medium   | a crash, hang or unbounded allocation where the input deserves an error |
| low      | a panic on a path documented to panic (the compiler on a malformed program), kept for triage |

A finding triaged as benign goes in `crates/fuzz/suppressions.txt` (or a campaign's own `<out>/suppressions.txt`), as a prefix of `<target> <key>` (`*` matches any run of characters) with a comment saying why: it is still recorded, under `findings/suppressed/`, and no longer counts.

`replay` runs a campaign against the current build: each recorded finding's case in a subprocess, saying whether it is fixed, still reproduces, or now gives another finding (a finding recorded for a worker that outgrew `--mem-limit-mb` replays without the limit, so it shows as fixed), then every corpus entry once. After a fix it says what the fix fixed; on a pull request it is a regression gate that re-runs every input a campaign ever found interesting, exiting with status 1 on a finding at `--fail-on` or worse.

## Measuring the fuzzer

A fuzzer that finds nothing is either facing sound code or blind. Three tools say which:

- **Resources.** The `leanvm-fuzz` binary counts every allocation (`resources.rs`). Each case notes the power of two its peak heap falls in, so a case that allocates more than any before joins the corpus and the campaign climbs toward expensive inputs, the denial-of-service bugs crash detection cannot see; a cheap case past 4 GiB is a finding, and `soundness-verifier-dos` holds the verifier and `replay_unchecked` to a budget linear in the proof on adversarial proofs. `stats.txt` shows each target's largest peak.
- **The guest's kill map.** The guest targets note where in `lean_ethereum.py` each refused run failed. `guest-coverage` sets those lines against every `assert`, `assert_in_k` and `assert_gpow` in the guest and lists the checks no forgery has ever made fail: where the next forgery strategies should aim, or checks nothing can reach.
- **Mutation analysis.** `fuzz/mutants.sh` disables one check of `crates/verifier` at a time (each `require` and each `transcript.checked()` guard, `fuzz/mutate_verifier.py`), rebuilds a copy of the tree, fuzzes the soundness targets for `--duration` seconds and records whether a finding killed the mutant. A surviving mutant is a check whose deletion no target notices. `--subject guest` does the same to the recursion guest, each `assert`, `assert_in_k` and `assert_gpow` of `lean_ethereum.py` in turn (`fuzz/mutate_guest.py`), against the guest and aggregation targets; every guest mutant proves its own child fixtures, so that sweep takes many hours. Run them on a fuzzing machine after a protocol or guest change, and keep the survivors list empty or explained.
- **Fingerprints.** Proofs are deterministic, so `cargo leanvm-fuzz fingerprint` (digests of every fast provable corpus program's bytecode and proof bytes) must print the same lines on every machine and at every thread count; `--compare <file>` diffs against another run. A difference between NEON, AVX2 and AVX-512 is a kernel that computes differently; one between two commits that change no program is a change to the proof, which `crates/verifier`, the Lean statement and the guest all have to follow.

## How a case works

A target is a function of a `Source`: every choice it makes (which program, which mutation, which stream index, which value) is read from a byte string. A case is a prefix (empty, or a corpus entry mutated AFL-style) followed by an endless tail from a PRNG seed, so `(prefix, seed)` replays it exactly, and the bytes it consumed replay it with no seed at all. Bulk data (blobs, messages) is expanded from one drawn word so it costs the recording eight bytes.

Targets report behaviours they reach as notes (`ctx.note(...)`: which mutation, which verifier error, which construct). A case that reaches a note new to its target joins the corpus (`<out>/corpus/<target>/`), and later cases are mostly its mutations: the stable-toolchain fuzzer's coverage signal. libFuzzer reads and writes the same directories, so its edge coverage and the notes feed each other.

## libFuzzer

`fuzz/` is a cargo-fuzz project (nightly, `cargo install cargo-fuzz`) with one binary per target, generated by `fuzz/sync-targets.sh` from `cargo leanvm-fuzz list`:

```bash
cd fuzz && ./sync-targets.sh
cargo +nightly fuzz run -O --debug-assertions decode-proof ../fuzz-out/corpus/decode-proof
```

A finding at or above `LEANVM_FUZZ_MIN_SEVERITY` (`medium` by default) is a crash to libFuzzer. `LEANVM_FUZZ_DIR` is the targets' cache directory, `LEANVM_FUZZ_DEPTH` their depth.

## The hand-written programs

`programs/` holds hand-written adversarial zkDSL programs, and the compiler's own `tests/programs/` are included too. Each states what must happen to it in annotations at the top (`programs.rs` documents them): `# expect: ok`, `exec-fail <message>`, `compile-error <message>`, `prove-fail <message>`, or `any`, its public input (discovered from the run when omitted) and its witness streams. `cargo leanvm-fuzz programs [--filter <name>]` checks every one once (`--file <path>` checks a program being written, before it joins the directory); the `dsl-corpus` target checks them over and over at random rates and statements, and the soundness targets attack their honest proofs. Add a program by dropping a file in: the build embeds the directory.

## The hooks

The malicious prover and aggregator need access no honest caller has, behind a `fuzzing` feature in each crate, never enabled outside this one:

- `fiat_shamir::tamper` (`leanvm_core::cpu::tamper::transcript`): a closure rewrites any scalar the next prover sends, after which the prover continues honestly from the challenges the forgery induces.
- `leanvm_core::cpu::tamper`: a closure edits the witness, every committed column and the virtual Keccak lanes, after the honest build and before the commitment. The prover's own consistency asserts on its witness (the bus GKR's roots, a side's leaf decomposition) are skipped once it has been edited, so the edited witness reaches the verifier instead of panicking the prover. `WitnessView::check` states the relation the protocol should enforce, which is what the target judges an accepted edit by.
- `rec_aggregation::fuzzing`: forge the guest's hint streams, run a node's guest without proving it (where a node's soundness is decided, at a fraction of a proof's cost), and build children with arbitrary claims, deferred claims and proofs.

## Targets

`cargo leanvm-fuzz list` prints them. Each group is a feature of this crate, so a group builds alone (`cargo build --profile fuzz -p leanvm-fuzz --no-default-features --features soundness`).

### `kernels`

Differential tests of the prover's kernels against plain references and the verifier's own field and hash.

| target | cost | attacks |
| ------ | ---- | ------- |
| `kernel-field` | cheap | K and E arithmetic, the batched and unreduced kernels, g-powers and inverses against a schoolbook reference and the verifier's field |
| `kernel-hash` | cheap | Keccak-256 one-shot, streaming, batched and from-state, and the permutation, against sha3 and a reference Keccak-f |
| `kernel-sponge` | cheap | the Fiat-Shamir duplex, compress and the DA membership challenge against a sponge built here from the permutation |
| `kernel-ntt` | cheap | the additive NTT: encode against naive novel-basis evaluation, forward then inverse, twiddles against subspace polynomials |
| `kernel-merkle` | cheap | the WHIR commitment root against an encode-and-hash reference, openings authenticated as the verifier does, mutated ones refused |
| `kernel-multilinear` | cheap | eq tables, MLE evaluation, packed dot products and the verifier's bytecode evaluation against naive sums |
| `kernel-bits` | cheap | bit transposes, the bit fold and streaming copies against naive loops |
| `kernel-parallel` | cheap | every thread-pool primitive on random counts and chunk sizes against a sequential loop |

### `decoders`

Every byte string a peer can send.

| target | cost | attacks |
| ------ | ---- | ------- |
| `decode-proof` | cheap | VM proof bytes, mutated honest encodings and garbage: no panic, every decode re-encodes to its input, a changed proof never verifies |
| `decode-aggregate` | medium | aggregate bytes with adversarial claims: no panic, decode round-trips, verify never panics and never accepts a garbage VM proof |
| `decode-signatures` | cheap | leanXMSS and leanSPHINCS keys and signatures from bytes: round trips, no panic, and one flipped bit of a real signature, key or message is refused |
| `lean-da` | medium | LeanDA commit on edge-sized payloads: errors not panics, deterministic, systematic, a codeword, the tree a plain rebuild gives, and the verifier's challenge |

### `dsl`

The zkDSL front end, compiler and runtime: the hand-written corpus, a Csmith-style generator of self-checking programs, metamorphic pairs, mutated sources (the recursion guest included) and raw parser input.

| target | cost | attacks |
| ------ | ---- | ------- |
| `dsl-corpus` | medium | every hand-written program meets its annotated expectation, its honest proof verifies, and only for its own public input |
| `dsl-gen` | medium | generated self-checking programs compile, run to the public input the generator computed, and prove |
| `dsl-metamorphic` | medium | two spellings of one generated program (inlined, unrolled, routed through buffers, constants refolded) publish the same public input, and a source compiles to one bytecode |
| `dsl-mutate` | medium | line and token mutations of the corpus and the recursion guest: parse never panics, compile panics are triaged, a mutant that compiles runs or errors, and one that runs proves |
| `dsl-parse` | cheap | raw bytes and grammar-shaped garbage (deep nesting, ** towers, huge literals, NUL, tabs) into parse and parse_const: no panic, hang or stack overflow |

### `isa`

Hand-assembled bytecode straight into the VM, bypassing the compiler.

| target | cost | attacks |
| ------ | ---- | ------- |
| `isa-random` | medium | generated straight-line, jumping, calling and KECCAK programs: no panic, memory as the generator computed, honest runs prove, proofs bind the input and every instruction |
| `isa-edge` | medium | bytecode at the edges: exact power-of-two lengths, table rows at powers of two, halting from another frame, self-loops, operands at u32::MAX, tiny main frames, non-power-of-two lengths |

### `soundness`

The malicious prover.

| target | cost | attacks |
| ------ | ---- | ------- |
| `soundness-proof-mutate` | medium | structured edits of an honest proof's stream and Merkle openings: verify rejects every changed proof, and neither verify nor replay panics |
| `soundness-transcript-tamper` | medium | a prover forging one or several transcript messages (announced sizes, root, GKR, sumchecks, Keccak, WHIR, nonces) and staying Fiat-Shamir consistent after: verify rejects |
| `soundness-witness-tamper` | medium | adversarial witness edits before commitment (single words, padding rows, coordinated memory lies, zeroed counts, row swaps): a proof verifies only if the edited witness still satisfies the relation |
| `soundness-wrong-statement` | medium | an honest proof against another public input or bytecode, and proofs by a prover whose Program carries a stale IV: verify rejects |
| `soundness-replay-consistency` | medium | replay_unchecked returns verify's Summary on honest proofs, never panics on mutated ones, and fails exactly where verify fails structurally |
| `soundness-determinism` | medium | a program proven twice is byte-identical, and its digest agrees across processes and thread counts |
| `soundness-verifier-dos` | medium | a garbage proof announcing sizes up to the caps, repaired round after round to walk deeper: replay_unchecked and verify stay within a budget linear in the proof, and never accept it |
| `soundness-keccak-batch` | medium | verify_keccak_batch accepts an honest standalone Keccak batch and rejects forged messages, tampered committed states and wrong shapes |

### `aggregation`

The recursion guest and the public aggregation API: the malicious aggregator, real child proofs built once per campaign and cached under `<out>/cache/aggregation/`, and 37 hand-written attack scenarios.

| target | cost | attacks |
| ------ | ---- | ------- |
| `guest-forge` | medium | a node's hint streams edited (a cell, an entry, a count, a slot, the claim lists): the guest refuses any witness but the honest one for its statement, and every statement nothing backs |
| `guest-child` | medium | a forged child (mutated proof, deferred claim, claims, DA root): whatever EthereumProof::verify rejects, the guest refuses, and the other way round |
| `aggregate-api` | medium | adversarial aggregate calls: an error of the documented kind, never a panic, never a run that publishes an unbacked claim; sampled valid nodes proven and verified |
| `aggregation-scenarios` | medium | hand-written aggregation attacks, each with its expected outcome |
