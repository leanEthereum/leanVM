use std::{
    env, fs,
    hint::black_box,
    ops::Range,
    time::{Duration, Instant},
};

use anyhow::{bail, ensure, Context, Result};
use lean_pq_comparison::{
    ensure_distinct_output_paths, lean_fixture_signers, lean_full_key_seed, BenchmarkReport,
    ComparisonReport, FixtureSet, LeanXmssClaim, LeanXmssInput, RecursiveAggregationReport,
    RunConfig, SampleSummary, KEY_CREATION_WORKLOAD, LIGHTHOUSE_REVISION, MIXED_CLAIM_SIGNATURES,
    RECURSIVE_CHILD_SIGNERS,
};

const SEMANTIC_WARNING: &str = "WARNING: leanVM aggregation of leanXMSS signatures generates zkVM proofs, while Lighthouse BLS aggregation combines elliptic-curve points; these operations do not have identical security semantics.";
const MIN_LIGHTHOUSE_BATCH_DURATION: Duration = Duration::from_millis(10);
const DISTINCT_CLAIM_VERIFY_WORKLOAD: &str = "distinct_claim_verify_conceptual";
const DISTINCT_VERIFY_NOTE: &str = "NOTE: distinct_claim_verify_conceptual and mixed_claim_verify_conceptual use Lighthouse aggregate_verify, an EF-test-only non-production path. Mixed-claim BLS verification includes aggregation of each claim's public keys. The fast independent_signatures_verify workload compares production-oriented BLS batch verification with LeanVM verification of the same independent signer-and-message tuples.";

fn main() -> Result<()> {
    let config =
        RunConfig::parse_from(env::args_os()).context("failed to parse runner arguments")?;
    run(config)
}

fn run(config: RunConfig) -> Result<()> {
    lean_pq::setup();

    let mixed_capacity = config.mixed_claim_counts.len() * 2;
    let mut comparisons = Vec::with_capacity(
        1 + (config.same_sizes.len() + config.distinct_sizes.len()) * 2 + mixed_capacity,
    );
    comparisons.push(measure_key_creation(config.samples)?);

    for &size in &config.same_sizes {
        let same_claim = FixtureSet::same_claim(size).with_context(|| {
            format!("failed to build same-claim fixtures for input size {size}")
        })?;
        let same_claim_inputs = same_claim.lean_inputs();
        let same_claim_expected = same_claim.lean_expected_claims();
        let same_claim_bls_message = same_claim.bls_messages()[0];
        let same_claim_bls_public_keys = same_claim.bls_public_keys().iter().collect::<Vec<_>>();

        let (aggregate_row, lean_aggregate, bls_aggregate) = measure_same_claim_aggregate(
            &same_claim,
            &same_claim_inputs,
            &same_claim_expected,
            &same_claim_bls_public_keys,
            config.samples,
            size,
            config.warmup_proofs,
        )?;
        comparisons.push(aggregate_row);
        comparisons.push(measure_same_claim_verify(
            &lean_aggregate,
            &bls_aggregate,
            &same_claim_expected,
            same_claim_bls_message,
            &same_claim_bls_public_keys,
            config.samples,
            size,
        )?);
    }

    for &size in &config.distinct_sizes {
        let distinct_claims = FixtureSet::distinct_claims(size).with_context(|| {
            format!("failed to build distinct-claim fixtures for input size {size}")
        })?;
        let distinct_inputs = distinct_claims.lean_inputs();
        let distinct_expected = distinct_claims.lean_expected_claims();
        let distinct_bls_messages = distinct_claims.bls_messages().to_vec();
        let distinct_bls_public_keys = distinct_claims.bls_public_keys().iter().collect::<Vec<_>>();

        let (aggregate_row, lean_aggregate, bls_aggregate) = measure_distinct_claim_aggregate(
            &distinct_claims,
            &distinct_inputs,
            &distinct_expected,
            &distinct_bls_messages,
            &distinct_bls_public_keys,
            config.samples,
            size,
            config.warmup_proofs,
        )?;
        comparisons.push(aggregate_row);
        comparisons.push(measure_distinct_claim_verify(
            &lean_aggregate,
            &bls_aggregate,
            &distinct_expected,
            &distinct_bls_messages,
            &distinct_bls_public_keys,
            config.samples,
            size,
        )?);
    }

    for &claim_count in &config.mixed_claim_counts {
        let mixed_claims = FixtureSet::mixed_claims(MIXED_CLAIM_SIGNATURES, claim_count)
            .with_context(|| {
                format!(
                    "failed to build mixed-claim fixtures for {} signatures across {} claims",
                    MIXED_CLAIM_SIGNATURES, claim_count
                )
            })?;
        let mixed_inputs = mixed_claims.lean_inputs();
        let mixed_expected = mixed_claims.lean_expected_claims();
        let (mixed_bls_messages, mixed_bls_public_keys) =
            mixed_claims.bls_grouped_claim_context()?;
        let mixed_bls_public_keys = mixed_bls_public_keys.iter().collect::<Vec<_>>();

        let (aggregate_row, lean_aggregate, bls_aggregate) = measure_mixed_claim_aggregate(
            &mixed_claims,
            &mixed_inputs,
            &mixed_expected,
            &mixed_bls_messages,
            &mixed_bls_public_keys,
            config.samples,
            config.warmup_proofs,
            claim_count,
        )?;
        comparisons.push(aggregate_row);
        comparisons.push(measure_mixed_claim_verify(
            &mixed_claims,
            &lean_aggregate,
            &bls_aggregate,
            &mixed_expected,
            config.samples,
            claim_count,
        )?);
    }

    let recursive_aggregations = measure_recursive_aggregations(
        &config.recursive_fan_ins,
        config.samples,
        config.warmup_proofs,
    )?;

    let report = BenchmarkReport {
        lighthouse_revision: LIGHTHOUSE_REVISION.to_owned(),
        samples: config.samples,
        proof_warmup: config.warmup_proofs,
        comparisons,
        recursive_aggregations,
        supplemental: Vec::new(),
    };

    println!("{SEMANTIC_WARNING}");
    println!("Pinned Lighthouse revision: {LIGHTHOUSE_REVISION}");
    println!("{}", proof_timing_mode_label(config.warmup_proofs));
    println!("{DISTINCT_VERIFY_NOTE}");
    if config.samples == 1 {
        println!("NOTE: a one-sample smoke run is not a publishable benchmark result.");
    }
    println!();
    println!("{}", report.to_table());

    write_report_files(&report, &config)
}

fn measure_key_creation(samples: usize) -> Result<ComparisonReport> {
    const WORKLOAD: &str = KEY_CREATION_WORKLOAD;
    let lighthouse_iterations =
        calibrate_batch_iterations(MIN_LIGHTHOUSE_BATCH_DURATION, |iterations| {
            let (elapsed, key) =
                time_last_value_batch(iterations, lighthouse_bls::SecretKey::random)?;
            black_box(key.public_key());
            Ok(elapsed)
        })
        .context("key_creation: Lighthouse calibration failed")?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    let mut retained_lean = None;
    let mut retained_lighthouse = None;
    for_each_paired_sample(
        samples,
        |sample| {
            let seed = lean_full_key_seed(sample).with_context(|| {
                format!("{WORKLOAD} (sample {sample}): failed to derive the LeanVM seed")
            })?;
            let start = Instant::now();
            let key = lean_pq::xmss::SecretKey::from_seed(black_box(seed));
            let duration = start.elapsed();
            black_box(key.public_key());
            lean_durations.push(duration);
            retained_lean.get_or_insert(key);
            Ok(())
        },
        |sample| {
            let key = record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| time_last_value_batch(iterations, lighthouse_bls::SecretKey::random),
                |key| {
                    black_box(key.public_key());
                    Ok(())
                },
            )
            .with_context(|| {
                format!("{WORKLOAD} (sample {sample}): Lighthouse key generation failed")
            })?;
            retained_lighthouse.get_or_insert(key);
            Ok(())
        },
    )?;

    let lean_key = retained_lean.context("key_creation retained no LeanVM secret key")?;
    let lighthouse_key =
        retained_lighthouse.context("key_creation retained no Lighthouse secret key")?;
    ComparisonReport::new(
        WORKLOAD,
        1,
        summarize(lean_durations, WORKLOAD, 1, "LeanVM")?,
        summarize(lighthouse_durations, WORKLOAD, 1, "Lighthouse")?,
        lean_key.to_bytes().len(),
        lighthouse_key.serialize().as_ref().len(),
    )
    .context("failed to assemble key_creation report")
}

fn measure_recursive_aggregations(
    fan_ins: &[usize],
    samples: usize,
    warmup_proofs: bool,
) -> Result<Vec<RecursiveAggregationReport>> {
    let Some(&maximum_fan_in) = fan_ins.iter().max() else {
        return Ok(Vec::new());
    };
    let mut children = Vec::with_capacity(maximum_fan_in);
    let mut claims = Vec::with_capacity(maximum_fan_in * RECURSIVE_CHILD_SIGNERS);

    for child_index in 0..maximum_fan_in {
        let signer_range = recursive_signer_range(child_index)?;
        let child_claims_start = claims.len();
        let inputs = lean_fixture_signers(signer_range, |_| 0).with_context(|| {
            format!("failed to create the fixture signers of recursive child proof {child_index}")
        })?;
        claims.extend(
            inputs
                .iter()
                .map(|(public_key, message, _)| (*public_key, *message)),
        );

        let child = lean_pq::aggregate(&[], &inputs, &[])
            .with_context(|| format!("failed to build recursive child proof {child_index}"))?;
        ensure_lean_claims(&child, &sorted_claims(&claims[child_claims_start..]))
            .with_context(|| format!("recursive child proof {child_index} lists wrong claims"))?;
        children.push(child);
    }

    fan_ins
        .iter()
        .map(|&fan_in| {
            let total_signers = fan_in
                .checked_mul(RECURSIVE_CHILD_SIGNERS)
                .context("recursive total signer count overflowed")?;
            let expected = sorted_claims(&claims[..total_signers]);
            let inputs = children[..fan_in].iter().collect::<Vec<_>>();
            run_optional_warmup(warmup_proofs, || {
                let aggregate = lean_pq::aggregate(&inputs, &[], &[]).with_context(|| {
                    format!("recursive fan-in {fan_in} proof warm-up failed")
                })?;
                ensure_lean_claims(&aggregate, &expected).with_context(|| {
                    format!("recursive fan-in {fan_in} proof warm-up lists wrong claims")
                })?;
                Ok(aggregate)
            })?;
            let mut durations = Vec::with_capacity(samples);
            let mut retained = None;
            for sample in 0..samples {
                let start = Instant::now();
                let aggregate = lean_pq::aggregate(&inputs, &[], &[]);
                let duration = start.elapsed();
                let aggregate = aggregate.with_context(|| {
                    format!(
                        "recursive same-claim aggregation (fan-in {fan_in}, sample {sample}) failed"
                    )
                })?;
                ensure_lean_claims(&aggregate, &expected).with_context(|| {
                    format!(
                        "recursive same-claim aggregation (fan-in {fan_in}, sample {sample}) lists wrong claims"
                    )
                })?;
                durations.push(duration);
                retained.get_or_insert(aggregate);
            }

            let retained = retained
                .with_context(|| format!("recursive fan-in {fan_in} retained no aggregate proof"))?;
            RecursiveAggregationReport::new(
                fan_in,
                RECURSIVE_CHILD_SIGNERS,
                summarize(
                    durations,
                    "recursive_same_claim_aggregate",
                    total_signers,
                    "LeanVM",
                )?,
                retained.to_bytes().len(),
            )
            .with_context(|| format!("failed to assemble recursive fan-in {fan_in} report"))
        })
        .collect()
}

fn recursive_signer_range(child_index: usize) -> Result<Range<usize>> {
    let start = child_index
        .checked_mul(RECURSIVE_CHILD_SIGNERS)
        .context("recursive signer range overflowed")?;
    let end = start
        .checked_add(RECURSIVE_CHILD_SIGNERS)
        .context("recursive signer range overflowed")?;
    Ok(start..end)
}

fn sorted_claims(claims: &[LeanXmssClaim]) -> Vec<LeanXmssClaim> {
    let mut sorted = claims.to_vec();
    sorted.sort_unstable();
    sorted
}

/// Checks the claims a fresh proof lists; `lean_pq::aggregate` proves exactly its inputs, so
/// this catches fixtures or inputs assembled wrongly.
fn ensure_lean_claims(aggregate: &lean_pq::Aggregate, expected: &[LeanXmssClaim]) -> Result<()> {
    ensure!(
        aggregate.xmss_claims() == expected,
        "LeanVM aggregate does not list exactly the expected leanXMSS claims"
    );
    ensure!(
        aggregate.sphincs_claims().is_empty(),
        "LeanVM aggregate lists unexpected leanSPHINCS claims"
    );
    Ok(())
}

fn write_report_files(report: &BenchmarkReport, config: &RunConfig) -> Result<()> {
    if let Some(path) = config.json_path.as_ref() {
        let json = serde_json::to_string_pretty(&report)
            .context("failed to serialize benchmark report as JSON")?;
        fs::write(path, json)
            .with_context(|| format!("failed to write JSON report to {}", path.display()))?;
    }

    if let Some(path) = config.action_json_path.as_ref() {
        let action_benchmarks = report
            .to_action_benchmarks()
            .context("failed to convert benchmark report to action JSON")?;
        let json = serde_json::to_string_pretty(&action_benchmarks)
            .context("failed to serialize benchmark action JSON")?;
        ensure_distinct_output_paths(
            config.json_path.as_deref(),
            config.action_json_path.as_deref(),
        )?;
        fs::write(path, json)
            .with_context(|| format!("failed to write action JSON report to {}", path.display()))?;
    }

    Ok(())
}

/// Times one LeanVM proof of `inputs`, then checks its claims outside the timed region.
fn timed_lean_aggregate(
    inputs: &[LeanXmssInput],
    expected: &[LeanXmssClaim],
) -> Result<(Duration, lean_pq::Aggregate)> {
    let start = Instant::now();
    let aggregate = lean_pq::aggregate(&[], inputs, &[]);
    let duration = start.elapsed();
    let aggregate = aggregate.context("LeanVM aggregation failed")?;
    ensure_lean_claims(&aggregate, expected)
        .context("LeanVM aggregate failed the post-timing claim check")?;
    Ok((duration, aggregate))
}

/// Times decoding one serialized LeanVM aggregate and verifying it against the expected
/// claims; success is the check.
fn timed_lean_verify(bytes: &[u8], expected: &[LeanXmssClaim]) -> Result<Duration> {
    let start = Instant::now();
    let aggregate = lean_pq::Aggregate::from_bytes(bytes, expected, &[]);
    let duration = start.elapsed();
    aggregate.context("LeanVM verification against the expected claims failed")?;
    Ok(duration)
}

fn measure_same_claim_aggregate(
    fixtures: &FixtureSet,
    lean_inputs: &[LeanXmssInput],
    lean_expected: &[LeanXmssClaim],
    bls_public_keys: &[&lighthouse_bls::PublicKey],
    samples: usize,
    size: usize,
    warmup_proofs: bool,
) -> Result<(
    ComparisonReport,
    lean_pq::Aggregate,
    lighthouse_bls::AggregateSignature,
)> {
    const WORKLOAD: &str = "same_claim_aggregate";
    let bls_message = fixtures.bls_messages()[0];

    let warmup_lean = run_optional_warmup(warmup_proofs, || {
        timed_lean_aggregate(lean_inputs, lean_expected)
            .map(|(_, aggregate)| aggregate)
            .with_context(|| format!("{WORKLOAD} (input size {size}): Lean proof warm-up failed"))
    })?;

    let lighthouse_iterations = calibrate_batch_iterations(
        MIN_LIGHTHOUSE_BATCH_DURATION,
        |iterations| {
            let (elapsed, aggregate) = time_last_value_batch(iterations, || {
                aggregate_bls(black_box(fixtures.bls_signatures()))
            })?;
            ensure!(
                aggregate.fast_aggregate_verify(bls_message, bls_public_keys),
                "{WORKLOAD} (input size {size}): Lighthouse calibration aggregate failed verification"
            );
            Ok(elapsed)
        },
    )
    .with_context(|| {
        format!("{WORKLOAD} (input size {size}): Lighthouse calibration failed")
    })?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    let mut retained_lean = None;
    let mut retained_lighthouse = None;
    for_each_paired_sample(
        samples,
        |sample| {
            let (duration, aggregate) = timed_lean_aggregate(lean_inputs, lean_expected)
                .with_context(|| format!("{WORKLOAD} (input size {size}, sample {sample})"))?;
            lean_durations.push(duration);
            retained_lean.get_or_insert(aggregate);
            Ok(())
        },
        |sample| {
            let aggregate = record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| {
                    time_last_value_batch(iterations, || {
                        aggregate_bls(black_box(fixtures.bls_signatures()))
                    })
                },
                |aggregate| {
                    ensure!(
                        aggregate.fast_aggregate_verify(bls_message, bls_public_keys),
                        "{WORKLOAD} (input size {size}, sample {sample}): Lighthouse aggregate failed post-timing verification"
                    );
                    Ok(())
                },
            )?;
            retained_lighthouse.get_or_insert(aggregate);
            Ok(())
        },
    )?;

    let timed_lean = retained_lean.with_context(|| {
        format!("{WORKLOAD} (input size {size}): retained no Lean aggregate proof")
    })?;
    let timed_lighthouse = retained_lighthouse.with_context(|| {
        format!("{WORKLOAD} (input size {size}): retained no Lighthouse aggregate signature")
    })?;
    let lean_artifact_bytes = timed_lean.to_bytes().len();
    let lighthouse_artifact_bytes = timed_lighthouse.serialize().len();
    let report = ComparisonReport::new(
        WORKLOAD,
        size,
        summarize(lean_durations, WORKLOAD, size, "Lean")?,
        summarize(lighthouse_durations, WORKLOAD, size, "Lighthouse")?,
        lean_artifact_bytes,
        lighthouse_artifact_bytes,
    )
    .with_context(|| format!("failed to assemble {WORKLOAD} report for input size {size}"))?;

    let verification_lean = warmup_lean.unwrap_or(timed_lean);
    Ok((report, verification_lean, timed_lighthouse))
}

fn measure_same_claim_verify(
    lean_aggregate: &lean_pq::Aggregate,
    bls_aggregate: &lighthouse_bls::AggregateSignature,
    lean_expected: &[LeanXmssClaim],
    bls_message: lighthouse_bls::Hash256,
    bls_public_keys: &[&lighthouse_bls::PublicKey],
    samples: usize,
    size: usize,
) -> Result<ComparisonReport> {
    const WORKLOAD: &str = "same_claim_verify";
    let lean_bytes = lean_aggregate.to_bytes();
    let lighthouse_iterations =
        calibrate_batch_iterations(MIN_LIGHTHOUSE_BATCH_DURATION, |iterations| {
            let (elapsed, all_valid) = time_bool_batch(iterations, || {
                black_box(bls_aggregate)
                    .fast_aggregate_verify(black_box(bls_message), black_box(bls_public_keys))
            })?;
            ensure!(
                all_valid,
                "{WORKLOAD} (input size {size}): Lighthouse calibration verification failed"
            );
            Ok(elapsed)
        })
        .with_context(|| {
            format!("{WORKLOAD} (input size {size}): Lighthouse calibration failed")
        })?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    for_each_paired_sample(
        samples,
        |sample| {
            let duration = timed_lean_verify(&lean_bytes, lean_expected)
                .with_context(|| format!("{WORKLOAD} (input size {size}, sample {sample})"))?;
            lean_durations.push(duration);
            Ok(())
        },
        |sample| {
            record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| {
                    time_bool_batch(iterations, || {
                        black_box(bls_aggregate).fast_aggregate_verify(
                            black_box(bls_message),
                            black_box(bls_public_keys),
                        )
                    })
                },
                |all_valid| {
                    ensure!(
                        *all_valid,
                        "{WORKLOAD} (input size {size}, sample {sample}): Lighthouse verification batch contained an invalid result"
                    );
                    Ok(())
                },
            )?;
            Ok(())
        },
    )?;

    ComparisonReport::new(
        WORKLOAD,
        size,
        summarize(lean_durations, WORKLOAD, size, "Lean")?,
        summarize(lighthouse_durations, WORKLOAD, size, "Lighthouse")?,
        lean_bytes.len(),
        bls_aggregate.serialize().len(),
    )
    .with_context(|| format!("failed to assemble {WORKLOAD} report for input size {size}"))
}

#[allow(clippy::too_many_arguments)]
fn measure_distinct_claim_aggregate(
    fixtures: &FixtureSet,
    lean_inputs: &[LeanXmssInput],
    lean_expected: &[LeanXmssClaim],
    bls_messages: &[lighthouse_bls::Hash256],
    bls_public_keys: &[&lighthouse_bls::PublicKey],
    samples: usize,
    size: usize,
    warmup_proofs: bool,
) -> Result<(
    ComparisonReport,
    lean_pq::Aggregate,
    lighthouse_bls::AggregateSignature,
)> {
    const WORKLOAD: &str = "distinct_claim_aggregate";

    let warmup_lean = run_optional_warmup(warmup_proofs, || {
        timed_lean_aggregate(lean_inputs, lean_expected)
            .map(|(_, aggregate)| aggregate)
            .with_context(|| format!("{WORKLOAD} (input size {size}): Lean proof warm-up failed"))
    })?;

    let lighthouse_iterations = calibrate_batch_iterations(
        MIN_LIGHTHOUSE_BATCH_DURATION,
        |iterations| {
            let (elapsed, aggregate) = time_last_value_batch(iterations, || {
                aggregate_bls(black_box(fixtures.bls_signatures()))
            })?;
            ensure!(
                aggregate.aggregate_verify(bls_messages, bls_public_keys),
                "{WORKLOAD} (input size {size}): Lighthouse calibration aggregate failed verification"
            );
            Ok(elapsed)
        },
    )
    .with_context(|| {
        format!("{WORKLOAD} (input size {size}): Lighthouse calibration failed")
    })?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    let mut retained_lean = None;
    let mut retained_lighthouse = None;
    for_each_paired_sample(
        samples,
        |sample| {
            let (duration, aggregate) = timed_lean_aggregate(lean_inputs, lean_expected)
                .with_context(|| format!("{WORKLOAD} (input size {size}, sample {sample})"))?;
            lean_durations.push(duration);
            retained_lean.get_or_insert(aggregate);
            Ok(())
        },
        |sample| {
            let aggregate = record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| {
                    time_last_value_batch(iterations, || {
                        aggregate_bls(black_box(fixtures.bls_signatures()))
                    })
                },
                |aggregate| {
                    ensure!(
                        aggregate.aggregate_verify(bls_messages, bls_public_keys),
                        "{WORKLOAD} (input size {size}, sample {sample}): Lighthouse aggregate failed post-timing verification"
                    );
                    Ok(())
                },
            )?;
            retained_lighthouse.get_or_insert(aggregate);
            Ok(())
        },
    )?;

    let timed_lean = retained_lean.with_context(|| {
        format!("{WORKLOAD} (input size {size}): retained no Lean aggregate proof")
    })?;
    let timed_lighthouse = retained_lighthouse.with_context(|| {
        format!("{WORKLOAD} (input size {size}): retained no Lighthouse aggregate signature")
    })?;
    let report = ComparisonReport::new(
        WORKLOAD,
        size,
        summarize(lean_durations, WORKLOAD, size, "Lean")?,
        summarize(lighthouse_durations, WORKLOAD, size, "Lighthouse")?,
        timed_lean.to_bytes().len(),
        timed_lighthouse.serialize().len(),
    )
    .with_context(|| format!("failed to assemble {WORKLOAD} report for input size {size}"))?;

    let verification_lean = warmup_lean.unwrap_or(timed_lean);
    Ok((report, verification_lean, timed_lighthouse))
}

#[allow(clippy::too_many_arguments)]
fn measure_mixed_claim_aggregate(
    fixtures: &FixtureSet,
    lean_inputs: &[LeanXmssInput],
    lean_expected: &[LeanXmssClaim],
    bls_messages: &[lighthouse_bls::Hash256],
    bls_public_keys: &[&lighthouse_bls::PublicKey],
    samples: usize,
    warmup_proofs: bool,
    claim_count: usize,
) -> Result<(
    ComparisonReport,
    lean_pq::Aggregate,
    lighthouse_bls::AggregateSignature,
)> {
    let (mut report, lean_aggregate, bls_aggregate) = measure_distinct_claim_aggregate(
        fixtures,
        lean_inputs,
        lean_expected,
        bls_messages,
        bls_public_keys,
        samples,
        MIXED_CLAIM_SIGNATURES,
        warmup_proofs,
    )?;
    report.workload = "mixed_claim_aggregate".to_owned();
    let report = report
        .with_claim_count(claim_count)
        .context("failed to record the mixed-claim aggregation shape")?;
    Ok((report, lean_aggregate, bls_aggregate))
}

fn measure_distinct_claim_verify(
    lean_aggregate: &lean_pq::Aggregate,
    bls_aggregate: &lighthouse_bls::AggregateSignature,
    lean_expected: &[LeanXmssClaim],
    bls_messages: &[lighthouse_bls::Hash256],
    bls_public_keys: &[&lighthouse_bls::PublicKey],
    samples: usize,
    size: usize,
) -> Result<ComparisonReport> {
    const WORKLOAD: &str = DISTINCT_CLAIM_VERIFY_WORKLOAD;
    let lean_bytes = lean_aggregate.to_bytes();
    let lighthouse_iterations =
        calibrate_batch_iterations(MIN_LIGHTHOUSE_BATCH_DURATION, |iterations| {
            let (elapsed, all_valid) = time_bool_batch(iterations, || {
                black_box(bls_aggregate)
                    .aggregate_verify(black_box(bls_messages), black_box(bls_public_keys))
            })?;
            ensure!(
                all_valid,
                "{WORKLOAD} (input size {size}): Lighthouse calibration verification failed"
            );
            Ok(elapsed)
        })
        .with_context(|| {
            format!("{WORKLOAD} (input size {size}): Lighthouse calibration failed")
        })?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    for_each_paired_sample(
        samples,
        |sample| {
            let duration = timed_lean_verify(&lean_bytes, lean_expected)
                .with_context(|| format!("{WORKLOAD} (input size {size}, sample {sample})"))?;
            lean_durations.push(duration);
            Ok(())
        },
        |sample| {
            record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| {
                    time_bool_batch(iterations, || {
                        black_box(bls_aggregate)
                            .aggregate_verify(black_box(bls_messages), black_box(bls_public_keys))
                    })
                },
                |all_valid| {
                    ensure!(
                        *all_valid,
                        "{WORKLOAD} (input size {size}, sample {sample}): Lighthouse verification batch contained an invalid result"
                    );
                    Ok(())
                },
            )?;
            Ok(())
        },
    )?;

    ComparisonReport::new(
        WORKLOAD,
        size,
        summarize(lean_durations, WORKLOAD, size, "Lean")?,
        summarize(lighthouse_durations, WORKLOAD, size, "Lighthouse")?,
        lean_bytes.len(),
        bls_aggregate.serialize().len(),
    )
    .with_context(|| format!("failed to assemble {WORKLOAD} report for input size {size}"))
}

fn measure_mixed_claim_verify(
    fixtures: &FixtureSet,
    lean_aggregate: &lean_pq::Aggregate,
    bls_aggregate: &lighthouse_bls::AggregateSignature,
    lean_expected: &[LeanXmssClaim],
    samples: usize,
    claim_count: usize,
) -> Result<ComparisonReport> {
    const WORKLOAD: &str = "mixed_claim_verify_conceptual";
    let lean_bytes = lean_aggregate.to_bytes();
    let lighthouse_iterations =
        calibrate_batch_iterations(MIN_LIGHTHOUSE_BATCH_DURATION, |iterations| {
            let (elapsed, all_valid) = time_bool_batch(iterations, || {
                fixtures
                    .verify_bls_grouped_claim_aggregate(black_box(bls_aggregate))
                    .unwrap_or(false)
            })?;
            ensure!(
                all_valid,
                "{WORKLOAD}: Lighthouse calibration verification failed"
            );
            Ok(elapsed)
        })
        .with_context(|| format!("{WORKLOAD}: Lighthouse calibration failed"))?;

    let mut lean_durations = Vec::with_capacity(samples);
    let mut lighthouse_durations = Vec::with_capacity(samples);
    for_each_paired_sample(
        samples,
        |sample| {
            let duration = timed_lean_verify(&lean_bytes, lean_expected)
                .with_context(|| format!("{WORKLOAD} (sample {sample})"))?;
            lean_durations.push(duration);
            Ok(())
        },
        |sample| {
            record_batched_sample(
                &mut lighthouse_durations,
                lighthouse_iterations,
                |iterations| {
                    time_bool_batch(iterations, || {
                        fixtures
                            .verify_bls_grouped_claim_aggregate(black_box(bls_aggregate))
                            .unwrap_or(false)
                    })
                },
                |all_valid| {
                    ensure!(
                        *all_valid,
                        "{WORKLOAD} (sample {sample}): Lighthouse verification batch contained an invalid result"
                    );
                    Ok(())
                },
            )?;
            Ok(())
        },
    )?;

    ComparisonReport::new(
        WORKLOAD,
        MIXED_CLAIM_SIGNATURES,
        summarize(lean_durations, WORKLOAD, MIXED_CLAIM_SIGNATURES, "Lean")?,
        summarize(
            lighthouse_durations,
            WORKLOAD,
            MIXED_CLAIM_SIGNATURES,
            "Lighthouse",
        )?,
        lean_bytes.len(),
        bls_aggregate.serialize().len(),
    )
    .with_context(|| format!("failed to assemble {WORKLOAD} report"))?
    .with_claim_count(claim_count)
    .context("failed to record the mixed-claim verification shape")
}

fn aggregate_bls(signatures: &[lighthouse_bls::Signature]) -> lighthouse_bls::AggregateSignature {
    let mut aggregate = lighthouse_bls::AggregateSignature::infinity();
    for signature in signatures {
        aggregate.add_assign(signature);
    }
    aggregate
}

fn calibrate_batch_iterations(
    minimum_duration: Duration,
    mut measure_batch: impl FnMut(usize) -> Result<Duration>,
) -> Result<usize> {
    const MAX_STEPS: usize = 8;
    const HEADROOM_NUMERATOR: u128 = 5;
    const HEADROOM_DENOMINATOR: u128 = 4;
    ensure!(
        !minimum_duration.is_zero(),
        "minimum batch duration must be greater than zero"
    );

    let mut iterations = 1usize;
    for _ in 0..MAX_STEPS {
        let elapsed = measure_batch(iterations)?;
        ensure!(
            !elapsed.is_zero(),
            "calibration batch duration must be greater than zero"
        );
        if elapsed >= minimum_duration {
            return Ok(iterations);
        }

        // Aim 25% above the acceptance threshold so normal timing jitter cannot
        // trap calibration in repeated just-under-threshold measurements.
        let numerator = minimum_duration
            .as_nanos()
            .checked_mul(iterations as u128)
            .and_then(|value| value.checked_mul(HEADROOM_NUMERATOR))
            .context("calibration iteration estimate overflowed")?;
        let denominator = elapsed
            .as_nanos()
            .checked_mul(HEADROOM_DENOMINATOR)
            .context("calibration iteration estimate overflowed")?;
        let estimated = numerator
            .checked_add(denominator - 1)
            .context("calibration iteration estimate overflowed")?
            / denominator;
        let estimated =
            usize::try_from(estimated).context("calibration iteration estimate exceeds usize")?;
        iterations = estimated.max(
            iterations
                .checked_add(1)
                .context("calibration iteration count overflowed")?,
        );
    }

    bail!("failed to calibrate a batch in {MAX_STEPS} steps")
}

fn normalize_batch_duration(elapsed: Duration, iterations: usize) -> Result<Duration> {
    ensure!(iterations > 0, "batch iterations must be greater than zero");
    ensure!(
        !elapsed.is_zero(),
        "batch duration must be greater than zero"
    );
    let nanoseconds = elapsed.as_nanos() / iterations as u128;
    ensure!(
        nanoseconds > 0,
        "normalized per-operation duration rounded to zero"
    );
    Ok(Duration::from_nanos(
        u64::try_from(nanoseconds).context("normalized duration exceeds u64 nanoseconds")?,
    ))
}

fn record_batched_sample<T>(
    durations: &mut Vec<Duration>,
    iterations: usize,
    run_batch: impl FnOnce(usize) -> Result<(Duration, T)>,
    validate: impl FnOnce(&T) -> Result<()>,
) -> Result<T> {
    let (elapsed, value) = run_batch(iterations)?;
    validate(&value)?;
    let duration = normalize_batch_duration(elapsed, iterations)?;
    durations.push(duration);
    Ok(value)
}

fn time_bool_batch(
    iterations: usize,
    mut operation: impl FnMut() -> bool,
) -> Result<(Duration, bool)> {
    ensure!(iterations > 0, "batch iterations must be greater than zero");
    let start = Instant::now();
    let mut all_valid = true;
    for _ in 0..iterations {
        all_valid &= black_box(operation());
    }
    Ok((start.elapsed(), all_valid))
}

fn time_last_value_batch<T>(
    iterations: usize,
    mut operation: impl FnMut() -> T,
) -> Result<(Duration, T)> {
    ensure!(iterations > 0, "batch iterations must be greater than zero");
    let start = Instant::now();
    let mut retained = None;
    for _ in 0..iterations {
        retained = Some(black_box(operation()));
    }
    let elapsed = start.elapsed();
    Ok((
        elapsed,
        retained.context("batch retained no operation result")?,
    ))
}

fn for_each_paired_sample(
    samples: usize,
    mut lean: impl FnMut(usize) -> Result<()>,
    mut lighthouse: impl FnMut(usize) -> Result<()>,
) -> Result<()> {
    ensure!(samples > 0, "at least one paired sample is required");
    for sample in 0..samples {
        if sample % 2 == 0 {
            lighthouse(sample)?;
            lean(sample)?;
        } else {
            lean(sample)?;
            lighthouse(sample)?;
        }
    }
    Ok(())
}

fn run_optional_warmup<T>(enabled: bool, warmup: impl FnOnce() -> Result<T>) -> Result<Option<T>> {
    if enabled {
        warmup().map(Some)
    } else {
        Ok(None)
    }
}

fn proof_timing_mode_label(warmup_proofs: bool) -> &'static str {
    if warmup_proofs {
        "PROOF TIMING MODE: steady-state (--warmup-proofs; one verified untimed Lean proof per aggregation workload and size)."
    } else {
        "PROOF TIMING MODE: no explicit proof warm-up (default; recorded samples may include process-local first-use effects)."
    }
}

fn summarize(
    durations: Vec<std::time::Duration>,
    workload: &str,
    size: usize,
    implementation: &str,
) -> Result<SampleSummary> {
    SampleSummary::from_durations(durations).with_context(|| {
        format!("failed to summarize {implementation} {workload} samples for input size {size}")
    })
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc, time::Duration};

    #[cfg(unix)]
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;

    #[test]
    fn recursive_children_use_disjoint_512_signer_ranges() {
        assert_eq!(recursive_signer_range(0).unwrap(), 0..512);
        assert_eq!(recursive_signer_range(1).unwrap(), 512..1_024);
        assert_eq!(recursive_signer_range(15).unwrap(), 7_680..8_192);
        assert!(recursive_signer_range(usize::MAX).is_err());
    }

    #[test]
    fn timed_verification_accepts_only_the_proven_claims() {
        lean_pq::setup();
        let fixtures = FixtureSet::distinct_claims(2).unwrap();
        let expected = fixtures.lean_expected_claims();
        let (_, aggregate) = timed_lean_aggregate(&fixtures.lean_inputs(), &expected).unwrap();
        let bytes = aggregate.to_bytes();

        let reversed = expected.iter().rev().copied().collect::<Vec<_>>();
        assert!(timed_lean_verify(&bytes, &expected).is_ok());
        assert!(timed_lean_verify(&bytes, &reversed).is_ok());

        assert!(timed_lean_verify(&bytes, &expected[..1]).is_err());
        let mut other_message = expected.clone();
        other_message[0].1[0] ^= 1;
        assert!(timed_lean_verify(&bytes, &other_message).is_err());

        assert!(timed_lean_verify(&bytes[..bytes.len() - 1], &expected).is_err());
        let mut tampered = bytes.clone();
        let middle = tampered.len() / 2;
        tampered[middle] ^= 1;
        assert!(timed_lean_verify(&tampered, &expected).is_err());
    }

    #[test]
    fn calibration_scales_batch_and_counts_invocations() {
        let observed = RefCell::new(Vec::new());

        let iterations = calibrate_batch_iterations(Duration::from_millis(10), |iterations| {
            observed.borrow_mut().push(iterations);
            Ok(Duration::from_millis(iterations as u64))
        })
        .unwrap();

        assert_eq!(iterations, 13);
        assert_eq!(*observed.borrow(), vec![1, 13]);
    }

    #[test]
    fn calibration_escapes_sub_threshold_timing_jitter() {
        let observed = RefCell::new(Vec::new());
        let elapsed_percent = [100_u128, 95, 94, 93, 92, 91, 90, 89];

        let iterations = calibrate_batch_iterations(Duration::from_millis(10), |iterations| {
            let call = observed.borrow().len();
            let elapsed_ns = (iterations as u128)
                .checked_mul(1_000)
                .and_then(|value| value.checked_mul(elapsed_percent[call]))
                .unwrap()
                / 100;
            let elapsed = Duration::from_nanos(u64::try_from(elapsed_ns).unwrap());
            observed.borrow_mut().push((iterations, elapsed));
            Ok(elapsed)
        })
        .unwrap();

        assert_eq!(iterations, 12_500);
        assert_eq!(
            observed
                .borrow()
                .iter()
                .map(|(iterations, _)| *iterations)
                .collect::<Vec<_>>(),
            vec![1, 12_500]
        );
        assert!(observed.borrow().last().unwrap().1 >= Duration::from_millis(10));
    }

    #[test]
    fn calibration_rejects_zero_target_and_zero_elapsed() {
        assert!(
            calibrate_batch_iterations(Duration::ZERO, |_| { Ok(Duration::from_nanos(1)) })
                .is_err()
        );
        assert!(
            calibrate_batch_iterations(Duration::from_millis(10), |_| { Ok(Duration::ZERO) })
                .is_err()
        );
    }

    #[test]
    fn calibration_reports_iteration_estimate_overflow() {
        let calls = RefCell::new(0);
        let error = calibrate_batch_iterations(Duration::MAX, |_| {
            *calls.borrow_mut() += 1;
            Ok(Duration::from_secs(2))
        })
        .unwrap_err();

        assert_eq!(*calls.borrow(), 2);
        assert!(error.to_string().contains("estimate overflowed"));
    }

    #[test]
    fn batch_duration_is_normalized_per_operation() {
        assert_eq!(
            normalize_batch_duration(Duration::from_millis(12), 4).unwrap(),
            Duration::from_millis(3)
        );
        assert!(normalize_batch_duration(Duration::ZERO, 1).is_err());
        assert!(normalize_batch_duration(Duration::from_nanos(1), 0).is_err());
        assert!(normalize_batch_duration(Duration::from_nanos(1), 2).is_err());
    }

    #[test]
    fn batch_recording_counts_invocations_and_excludes_invalid_result() {
        let mut durations = Vec::new();
        let mut invocations = 0;
        let value = record_batched_sample(
            &mut durations,
            4,
            |iterations| {
                invocations += iterations;
                Ok((Duration::from_millis(12), true))
            },
            |valid| {
                ensure!(*valid, "invalid batch");
                Ok(())
            },
        )
        .unwrap();

        assert!(value);
        assert_eq!(invocations, 4);
        assert_eq!(durations, vec![Duration::from_millis(3)]);

        let error = record_batched_sample(
            &mut durations,
            4,
            |_| Ok((Duration::from_millis(12), false)),
            |valid| {
                ensure!(*valid, "invalid batch");
                Ok(())
            },
        )
        .unwrap_err();
        assert!(error.to_string().contains("invalid batch"));
        assert_eq!(durations, vec![Duration::from_millis(3)]);
    }

    #[test]
    fn timed_bool_batch_invokes_every_operation_and_tracks_any_failure() {
        let mut invocations = 0;
        let (_, all_valid) = time_bool_batch(5, || {
            invocations += 1;
            invocations != 3
        })
        .unwrap();

        assert_eq!(invocations, 5);
        assert!(!all_valid);
    }

    #[test]
    fn timed_last_value_batch_invokes_every_operation_and_retains_last() {
        let mut invocations = 0;
        let (_, retained) = time_last_value_batch(4, || {
            invocations += 1;
            invocations
        })
        .unwrap();

        assert_eq!(invocations, 4);
        assert_eq!(retained, 4);
    }

    #[test]
    fn paired_samples_alternate_bls_and_lean_order() {
        let order = Rc::new(RefCell::new(Vec::new()));
        let lean_order = Rc::clone(&order);
        let lighthouse_order = Rc::clone(&order);

        for_each_paired_sample(
            3,
            |sample| {
                lean_order.borrow_mut().push(format!("lean-{sample}"));
                Ok(())
            },
            |sample| {
                lighthouse_order
                    .borrow_mut()
                    .push(format!("lighthouse-{sample}"));
                Ok(())
            },
        )
        .unwrap();

        assert_eq!(
            *order.borrow(),
            vec![
                "lighthouse-0",
                "lean-0",
                "lean-1",
                "lighthouse-1",
                "lighthouse-2",
                "lean-2",
            ]
        );
    }

    #[test]
    fn optional_proof_warmup_runs_exactly_once_only_when_enabled() {
        let mut invocations = 0;
        let disabled = run_optional_warmup(false, || {
            invocations += 1;
            Ok(1)
        })
        .unwrap();
        assert!(disabled.is_none());
        assert_eq!(invocations, 0);

        let enabled = run_optional_warmup(true, || {
            invocations += 1;
            Ok(2)
        })
        .unwrap();
        assert_eq!(enabled, Some(2));
        assert_eq!(invocations, 1);
    }

    #[test]
    fn proof_timing_mode_labels_are_accurate() {
        let default = proof_timing_mode_label(false);
        assert!(default.contains("no explicit proof warm-up"));
        assert!(!default.contains("first-use-inclusive"));

        let steady_state = proof_timing_mode_label(true);
        assert!(steady_state.contains("steady-state"));
        assert!(steady_state.contains("--warmup-proofs"));
    }

    #[test]
    fn distinct_verification_labels_expose_lighthouse_status() {
        assert_eq!(
            DISTINCT_CLAIM_VERIFY_WORKLOAD,
            "distinct_claim_verify_conceptual"
        );
        assert!(DISTINCT_VERIFY_NOTE.contains("EF-test"));
        assert!(DISTINCT_VERIFY_NOTE.contains("non-production"));
        assert!(DISTINCT_VERIFY_NOTE.contains("independent_signatures_verify"));
    }

    #[cfg(unix)]
    #[test]
    fn report_write_rechecks_a_dangling_symlink_before_action_output() {
        use std::os::unix::fs::symlink;

        let directory = TestDirectory::new("dangling-symlink");
        let full = directory.path().join("full.json");
        let action = directory.path().join("action.json");
        symlink("full.json", &action).unwrap();
        let config = RunConfig::parse_from([
            "slow-comparison",
            "--json",
            full.to_str().unwrap(),
            "--action-json",
            action.to_str().unwrap(),
        ])
        .unwrap();
        let lean = SampleSummary::from_durations([Duration::from_millis(2)]).unwrap();
        let lighthouse = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();
        let report = BenchmarkReport {
            lighthouse_revision: LIGHTHOUSE_REVISION.to_owned(),
            samples: 1,
            proof_warmup: false,
            comparisons: vec![ComparisonReport::new(
                "same_claim_verify",
                1,
                lean,
                lighthouse,
                1,
                1,
            )
            .unwrap()],
            recursive_aggregations: vec![],
            supplemental: vec![],
        };

        let error = write_report_files(&report, &config).unwrap_err();

        assert!(error
            .to_string()
            .contains("--json and --action-json must write to different paths"));
        let preserved: BenchmarkReport = serde_json::from_slice(&fs::read(&full).unwrap()).unwrap();
        assert_eq!(preserved, report);
    }

    #[cfg(unix)]
    struct TestDirectory(PathBuf);

    #[cfg(unix)]
    impl TestDirectory {
        fn new(label: &str) -> Self {
            static NEXT_ID: AtomicU64 = AtomicU64::new(0);
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "lean-pq-comparison-runner-{label}-{}-{id}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    #[cfg(unix)]
    impl Drop for TestDirectory {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
}
