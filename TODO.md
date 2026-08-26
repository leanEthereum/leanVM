# TODO

## Perf

- Opti WHIR https://github.com/tcoratger/whir-p3/issues/303 and https://github.com/tcoratger/whir-p3/issues/306 ?
- Avoid the embedding overhead in logup, when denominators = "c - index"
- Fancy zkDSL compiler opti: within each function frame, we could assign one (if any) of the dynamic allocation to the part of the memory coming just after the current frame. This way, the pointer would not be hinted, but rather constant at compile time -> more efficient memory acceses. We could even even have a special keyword (instead of just "Array") to specify which dynamic allocation should benefit from this optimization. Difficulty: that would require to manipulate segments of memory at runtime. Maybe apply this idea to function call and even to loops?
- Further use delayed modular reduction (cf. https://github.com/Plonky3/Plonky3/pull/1592, https://github.com/Plonky3/Plonky3/pull/1597, etc) ?

## Security:

- 128 bits security? (currently 124)
- Fiat Shamir: add a claim tracing feature, to ensure all the claims are indeed checked (Lev)
- Double Check AIR constraints, logup overflows etc
- Do we need to enforce some values at the first row of the dot-product table?
- Formal Verification
- Padd with noop cycles to always ensure memory size >= bytecode size (liveness), and ensure this condition is checked by the verifier (soundness)
- Rewrite the compiler, it's bad right now.
- double check single-message / multi-message dispatch, and try to simplify the various data layouts

## Tooling

- The clippy config never reaches the member crates. Root `Cargo.toml` has `[lints.clippy]`
  (`all`/`nursery`/`pedantic` at warn, plus the `allow` list), but that is a *package*-level
  table, so it applies only to the root `lean-multisig` package. `[workspace.lints]` carries
  just the `rust.*` and `rustdoc.*` keys, so every crate under `crates/` writing
  `[lints] workspace = true` inherits those alone and gets no clippy nursery/pedantic.
  Moving the table to `[workspace.lints.clippy]` would fix it, but surfaces a backlog across
  the 19 member crates, so it wants doing deliberately rather than as a drive-by.

- `#[ignore]` carries two meanings, so CI selects slow tests by naming a binary. It marks both
  "this is a benchmark, never run it in CI" (`benchmark_poseidons.rs`, `benchmark.rs`,
  `grinding.rs`, `wots.rs`, `quotient_gkr`, `test_zkvm.rs`) and "this is a real test, too slow
  for a local run, but CI must run it" (`lean_multisig_api`'s two `LEAF_TARGET` boundary tests).
  Because `--include-ignored` cannot tell them apart, `rust.yml`'s `Ignored slow tests` step
  names one test binary explicitly. That is correct today but is a hand-maintained allowlist:
  the next ignored-but-required test is silently not run, with nothing failing to say so.
  Distinguishing them — keep `#[ignore]` for benchmarks, gate slow-but-required tests behind a
  `slow-tests` feature — would let CI run one command with no per-binary list.

# Ideas

- About range checks, that can currently be done in 3 cycles (see 2.5.3 of the zkVM pdf) + 3 memory cells used. For small ranges we can save 2 memory cells.
- Avoid committing to the 3 index columns, and replace it by a sumcheck? Idea by Georg (Powdr). Advantage: Less commitment surface. Drawback: increase the number of instances in the final WHIR batch opening -> proof size overhead
  
