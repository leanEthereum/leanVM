# leanVM leanXMSS and Lighthouse BLS benchmarks

This crate compares leanXMSS signatures and their leanVM aggregation, through the
Rust `lean-pq` binding, with Lighthouse's `bls`
wrapper pinned to revision
`e423a66763bb1bd780492d635123f208d80c3538` and its default Supranational
backend.

These are performance comparisons, not claims of equivalent security
semantics. leanVM aggregation generates zkVM proofs, whereas BLS
aggregation combines elliptic-curve points.

## Fast paired-operation benchmarks

Run the Criterion suite in release mode:

```bash
cargo bench -p lean-pq-comparison --bench comparison
```

The fast suite compares paired signing, raw-signature serialization and
deserialization, single-signature verification, and
verification of `1,8,16` independent signer-and-message tuples. For the last
workload, LeanVM verifies every raw leanXMSS signature and Lighthouse uses its
production batch-verification API. Aggregate proof generation and verification
are measured by the slow paired comparison below.

## Key-creation and slow paired comparison

The practical default generates three leanXMSS keys and runs three proof
samples at sizes `1,8,16` on both axes:

```bash
cargo run --release -p lean-pq-comparison --bin slow_comparison
```

Use independent options to opt into larger same-claim proofs:

```bash
cargo run --release -p lean-pq-comparison --bin slow_comparison -- \
  --samples 3 \
  --same-sizes 32,64,128,256,512 \
  --distinct-sizes 1,8,16 \
  --mixed-claim-counts 8,16 \
  --recursive-fan-ins 2,4,8,16
```

`--mixed-claim-counts 8,16` adds mixed workloads with 512 raw signatures
spread evenly across 8 claims (64 signers per claim) and 16 claims (32 signers
per claim). LeanVM proves all 512 signatures, whatever their messages, in one
`lean_pq::aggregate` call. The BLS side aggregates the
same 512 signatures. For BLS verification, timing includes grouping and
aggregating each claim's public keys before verifying the single aggregate
against the requested number of message-and-aggregated-key pairs. Counts must
be unique integers greater than 1 that divide 512 evenly.

`--recursive-fan-ins 2,4,8,16` measures LeanVM's proof-to-proof recursion.
The runner first creates the maximum requested number of child proofs outside
the timed region. Every child aggregates 512 distinct leanXMSS signers of the
same claim (the identical message), and signer sets are disjoint between
children. Each timed sample then
validates and combines the requested number of pre-built children into one new
proof. The report records the merge median and serialized output-proof size for
each fan-in. With `--warmup-proofs`, one additional merge at each fan-in runs
before its recorded samples. Fan-ins must be unique integers from 2 through
`lean_pq::MAX_CHILDREN` (16).
The option is disabled by default for local runs because preparing the child
proofs is slow.

Key generation is always part of this runner. It times
`xmss::SecretKey::from_seed` for one key beside Lighthouse BLS key generation
and reports the serialized key size. A leanXMSS key covers `2^32` leaf indices
and serializes to its 32-byte seed; key generation builds only its top tree,
and each bottom tree is built the first time the key signs in it. The large
LeanVM proof sweep can take substantial time and memory. It is never part of
the default run. `--same-sizes` and `--distinct-sizes` accept unique positive
sizes through 512. Each option defaults independently to `1,8,16`. The
backward-compatible `--sizes` option sets both axes and cannot be combined
with either specific size option.

Add `--warmup-proofs` for steady-state proof measurements. Without it, no
explicit Lean proof warm-up runs; recorded samples may include process-local
first-use effects. Add `--json PATH` to save the unchanged machine-readable
report alongside the table printed to stdout. Add `--action-json PATH` to save
an independent `customSmallerIsBetter` export for optional external consumers;
the two output paths must resolve to different files. The current CI dashboard
does not use this export. Fixture setup and post-timing claim checks are
outside the timed region. The aggregation and independent-signature fixtures
sign with real leanXMSS keys, one per signer-and-message pair, each derived
from its own seed in a seed domain the full keys never use. Every fixture
signature lies in its key's first bottom tree (leaf indices 0 through 15), so
each fixture key builds one bottom tree. Fixture generation is untimed and runs
on every available core; a 512-signer fixture still takes noticeable time.
Full keys remain for the timed key-generation workload and the fast sign,
serialization, and single-verify benchmarks. An aggregate's encoding is its
proof alone, so aggregate verification times
`lean_pq::Aggregate::from_bytes` given the expected signer-and-message claims:
it decodes the proof and verifies it against exactly those claims, just as
Lighthouse verifies against the expected messages and public keys. Lighthouse
operations are calibrated in batches of at least 10 ms and reported per
operation.

The local equivalent of the slow PR job is:

```bash
cargo build --release -p lean-pq-comparison --bin slow_comparison
/usr/bin/time -v -o resource-usage.txt target/release/slow_comparison \
  --samples 3 \
  --same-sizes 1,8,16,256,512 \
  --distinct-sizes 1,8,16 \
  --mixed-claim-counts 8,16 \
  --recursive-fan-ins 2,4,8,16 \
  --warmup-proofs \
  --json full.json
```

`resource-usage.txt` contains the process-wide peak resident set size for the
complete slow suite, not a per-workload attribution. CI normalizes this value to
bytes together with `full.json` for the dashboard. GNU `/usr/bin/time` reports
RSS in KiB; normalization rejects missing, duplicate, malformed, zero, or
unrepresentable measurements.

`distinct_claim_verify_conceptual` uses Lighthouse `aggregate_verify`, which
Lighthouse documents as an EF-test-only, non-production path. The fast
`independent_signatures_verify` workload provides the production-oriented
comparison: LeanVM verifies the same independent signer-and-message tuples
that Lighthouse verifies with its batch API.

The 512-signer fixture-shape regression builds and validates every raw leanXMSS
fixture signature, so ordinary `cargo test` skips it. Run it explicitly when
changing fixture construction:

```bash
cargo test -p lean-pq-comparison --test fixtures \
  same_claim_fixtures_support_the_expanded_signer_limit -- --ignored --exact
```

When publishing results, include the CPU, operating system, Rust compiler, run
mode, sample count, and whether proof warm-up was enabled.

## Pull request benchmark CI

Pull request benchmarks are opt-in. Add the `run-benchmarks` label to a
same-repository pull request to run the fast suite and three warmed-up
slow-suite samples on the dedicated runner labeled
`size-attester7870-x64`.
New commits rerun the suites while the label is present. Removing the label or
closing the pull request cancels an active run. Fork pull requests are skipped
because benchmark jobs execute repository code on that machine. Same-claim
proofs use sizes `1,8,16,256,512`;
distinct-claim proofs use `1,8,16`, and the mixed workloads use 512 signatures
across 8 and 16 claims. Both place their current measurements in the
job summary. The slow job also combines 2, 4, 8, and 16 pre-built same-claim
proofs, each representing 512 different signers. The normalized slow artifact
includes overall peak RSS. Both
jobs retain their raw output, normalized data, and environment metadata as
workflow artifacts for 14 days. Fast dashboard data is normalized from
Criterion's structured estimates; slow artifacts contain the full numeric
report and GNU time resource report.

These dedicated-runner measurements are informational. They do not use an
automated performance threshold and do not gate merging. The pull request
workflow has read-only repository permissions and never updates the public
dashboard.

Benchmark execution, proof/signature validation, report conversion, and
artifact failures still fail their jobs. Each environment sidecar records the
commit, runner OS and architecture, runner image name and version, CPU, kernel,
Rust and Cargo versions, the manifest-derived Lighthouse revision, suite,
sample count, applicable size axes, and proof-warmup mode.

## Current-results dashboard

The trusted benchmark workflow has two modes:

- Relevant pushes to `main` run both suites on the dedicated runner
  labeled `size-attester7870-x64`. With one matching runner, the jobs execute
  one at a time. The slow suite uses three samples and proof warm-up, with same-claim
  sizes `1,8,16,256,512`, distinct-claim sizes `1,8,16`, and the fixed
  512-signature mixed workloads with 8 and 16 claims. It also measures 2, 4, 8,
  and 16 pre-built same-claim child proofs with 512 disjoint signers per child.
  Fast artifacts are retained for 30 days and slow artifacts for 90 days.
- `workflow_dispatch` accepts `fast`, `slow`, or `all`, plus the slow sample
  count (minimum 3) and independent same/distinct size lists. Manual slow runs
  also accept a recursive fan-in list, defaulting to `2,4,8,16`, and always use
  proof warm-up. One-sample smoke runs remain local-only and cannot be published
  by the workflow.

For example, this explicitly opts into the large same-claim sweep:

```bash
gh workflow run benchmarks-history.yml \
  -f suite=slow \
  -f samples=3 \
  -f same_sizes=32,64,128,256,512 \
  -f distinct_sizes=1,8,16 \
  -f recursive_fan_ins=2,4,8,16
```

That full sweep can take substantial time and memory. Same-claim sizes
`32,64,128` and distinct-claim sizes above 16 remain manual additions.

Each successful measurement produces a validated `dashboard.json`. A separate
publication job downloads only successful artifacts, checks out `gh-pages`, and
replaces `data/fast.json` and/or `data/slow.json`. A fast-only run preserves the
last slow result and vice versa. It also installs the static dashboard as the
branch-root `index.html`; it does not execute measured repository code.

The public page is <https://ethereum.github.io/lean-pq-bindings/>. It shows
only the newest result for each suite: LeanVM and Lighthouse timings and ratios
grouped by operation family; serialized secret-key, public-key, and raw-signature
sizes; LeanVM proof and aggregate BLS signature sizes; overall slow-suite peak
RSS; recursive proof-to-proof aggregation at fan-ins 2, 4, 8, and 16; and the
measurement environment. The LeanVM key-creation row times deriving one
leanXMSS key from its seed and reports its 32-byte serialized size. A short glossary
defines the aggregation and verification workloads. There are no
commit-over-commit plots. The first publication removes the old nested
`dev/bench` pages.

### One-time Pages setup

Create an orphan `gh-pages` branch. To avoid disturbing a working checkout, do
this in a temporary clone (set `REPOSITORY_URL` first):

```bash
benchmark_pages_dir=$(mktemp -d)
git clone "$REPOSITORY_URL" "$benchmark_pages_dir/repo"
cd "$benchmark_pages_dir/repo"
git switch --orphan gh-pages
git rm -rf .
touch .nojekyll
git add .nojekyll
git commit -m 'chore: initialize benchmark dashboard'
git push origin gh-pages
```

In repository settings, configure GitHub Pages to deploy from the `gh-pages`
branch and its root directory. Ensure GitHub Actions may use the workflow's
declared write permission. Trusted `main` pushes and manual runs may then update
`gh-pages`; PR workflows retain `contents: read` and receive no secrets.
