# Lighthouse BLS Comparison Benchmarks

## Goal

Add reproducible Rust benchmarks that show the relative performance of leanMultisig and the BLS implementation used by Lighthouse. The comparison must use Lighthouse's public `bls` wrapper with its default `supranational` (`blst`) backend, not `blst` directly.

The benchmark results must keep semantically different operations separate. In particular, leanMultisig aggregation generates a zkVM proof, while BLS aggregation combines elliptic-curve points. Their latency ratio is useful operational information, but it is not a comparison of identical security semantics.

## Architecture

Create a standalone `benchmarks/comparison` Rust crate and add it to the root Cargo workspace. This keeps benchmark-only dependencies out of the published language bindings.

The crate will depend on:

- The local `lean-pq` Rust facade by path.
- Lighthouse's `bls` package at commit `e423a66763bb1bd780492d635123f208d80c3538` from the `stable` branch.
- Criterion for statistically sampled fast operations.
- A small serialization dependency for machine-readable slow-runner results.

The crate layout will be:

```text
benchmarks/comparison/
├── Cargo.toml
├── README.md
├── src/
│   ├── lib.rs
│   └── bin/slow_comparison.rs
├── benches/comparison.rs
└── tests/fixtures.rs
```

Shared fixture builders, validation helpers, timing summaries, and report types will live in `src/lib.rs`. Criterion and the slow runner will therefore use the same inputs and validation rules.

## Workloads

All workloads use deterministic fixtures. Each signer receives a unique nonzero 32-byte key input. Same-claim cases share one 32-byte signing root. Distinct-claim cases use unique signing roots and Lean slots.

The suite will compare:

| Workload | leanMultisig | Lighthouse BLS |
| --- | --- | --- |
| Key creation | Deterministic XMSS key from seed | Deterministic BLS secret key |
| Public-key derivation | Derive the XMSS public key | Derive the BLS public key |
| Signing | Sign a 32-byte claim | Sign the same 32-byte signing root |
| Raw serialization | Encode/decode a signature with external context | Encode/decode a compressed signature |
| Single verification | Verify one signer and claim | Verify one signer and signing root |
| Same-claim aggregation | Generate a recursive proof | Combine BLS signatures |
| Same-claim verification | Verify the proof and exact signer set | Fast aggregate verification |
| Distinct-claim aggregation | Generate a multi-claim proof | Combine distinct-message BLS signatures |
| Distinct-claim verification | Verify exact claim/signer groups | Aggregate verification |
| Production BLS batch verification | Not a direct Lean operation | Lighthouse `verify_signature_sets` |

The distinct-message report will label Lighthouse aggregate verification as a conceptual comparison because Lighthouse documents that method as an EF-test path. It will separately report `verify_signature_sets`, Lighthouse's production-oriented batch-verification path.

## Measurement model

Criterion will measure fast operations. Fixtures are constructed outside timed loops, inputs and outputs pass through `black_box`, and mutable operations receive fresh cloned state where required.

Expensive proof generation will use a dedicated release-mode runner instead of Criterion's default sampling. It will measure paired Lean and BLS operations at 1, 8, and 16 inputs. The runner will:

- Initialize Lean proving outside timed regions.
- Construct keys, signatures, claims, and expected signer sets outside timed regions.
- Perform an untimed warm-up where practical.
- Collect three samples by default, with a command-line override.
- Record each sample and report the median.
- Report operations per second, the Lean/BLS latency ratio, and serialized artifact sizes.
- Print a human-readable table and emit JSON suitable for later plotting or archival.
- Verify every produced artifact outside its timed region before accepting the sample.

The runner will reject zero samples and distinct-claim counts above leanMultisig's limit of 16. Any setup, construction, proving, serialization, or verification error will include workload and input-size context and terminate with a nonzero exit status.

## Correctness and maintenance

Before any measurement, fixtures will be checked by signing and verifying once. This prevents invalid inputs or a fast rejection path from being recorded as successful cryptographic work.

Ordinary tests will cover:

- Deterministic and unique fixture generation.
- Requested signer and claim counts.
- Successful raw XMSS and BLS verification.
- Timing-summary and ratio calculations.
- JSON report serialization.
- Rejection of invalid runner arguments and unsupported claim counts.

Expensive zkVM aggregation will not run during ordinary `cargo test` or CI. Benchmark targets will still be compiled as part of implementation verification so dependency or API drift is caught.

The benchmark README will document exact release-mode commands, expected runtime, sample configuration, excluded setup costs, backend and commit pins, semantic caveats, and the need to publish CPU, OS, and compiler details alongside results. Generated reports will not be committed automatically.

