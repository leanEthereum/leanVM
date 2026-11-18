//! Benchmark support for comparing leanVM's leanXMSS aggregation with Lighthouse BLS.
//!
//! This crate supports the repository's comparison benchmarks and is not a
//! supported public API.

use std::{
    borrow::Cow,
    ffi::{OsStr, OsString},
    num::NonZeroUsize,
    ops::Range,
    path::{Path, PathBuf},
    thread,
    time::Duration,
};

use anyhow::{anyhow, ensure, Context, Result};
use serde::{Deserialize, Serialize};

pub const MAX_SIGNERS: usize = 512;
pub const MIXED_CLAIM_SIGNATURES: usize = 512;
pub const MIXED_CLAIM_COUNTS: [usize; 2] = [8, 16];
pub const RECURSIVE_CHILD_SIGNERS: usize = 512;
pub const MAX_RECURSIVE_FAN_IN: usize = lean_pq::MAX_CHILDREN;
pub const RECURSIVE_AGGREGATION_WORKLOAD: &str = "recursive_same_claim_aggregate";
pub const KEY_CREATION_WORKLOAD: &str = "key_creation";
pub const LIGHTHOUSE_REVISION: &str = "e423a66763bb1bd780492d635123f208d80c3538";
/// The leaf indices fixture signers sign at, all in a key's first bottom tree, so a fixture
/// key builds one bottom tree only.
pub const FIXTURE_FIRST_LEAF: lean_pq::xmss::LeafIndex = 0;
pub const FIXTURE_LAST_LEAF: lean_pq::xmss::LeafIndex = 15;

/// Seed domains: a leanXMSS seed must back one key only, so fixture keys and full keys
/// never share a seed.
const FIXTURE_SEED_DOMAIN: u8 = 1;
const FULL_KEY_SEED_DOMAIN: u8 = 2;

/// Returns deterministic, nonzero 32-byte material: BLS fixture keys and messages.
pub fn deterministic_key_material(index: usize) -> Result<[u8; 32]> {
    indexed_bytes(index)
}

/// Returns the seed of full leanXMSS key `index`, which no fixture signer's key uses.
pub fn lean_full_key_seed(index: usize) -> Result<[u8; lean_pq::xmss::SEED_LEN]> {
    lean_seed(FULL_KEY_SEED_DOMAIN, 0, index)
}

/// Returns untimed fixture signer `index` signing message `message_index`.
///
/// The key is a real leanXMSS key derived from its own seed: each signer-and-message pair
/// has one, so a key only ever signs one message. It signs at leaf index
/// `FIXTURE_FIRST_LEAF + message_index % 16`, in its first bottom tree.
pub fn lean_fixture_signer(index: usize, message_index: usize) -> Result<LeanXmssInput> {
    let message = indexed_bytes(message_index)?;
    let seed = lean_seed(FIXTURE_SEED_DOMAIN, message_index, index)?;
    let leaf_span = usize::try_from(FIXTURE_LAST_LEAF - FIXTURE_FIRST_LEAF + 1)?;
    let leaf_index =
        FIXTURE_FIRST_LEAF + lean_pq::xmss::LeafIndex::try_from(message_index % leaf_span)?;
    let key = lean_pq::xmss::SecretKey::from_seed(seed);
    let signature = key.sign(&message, leaf_index);
    Ok((key.public_key(), message, signature))
}

/// Returns fixture signers `signers`, signer `index` signing message `message_index(index)`,
/// in order.
///
/// Each real key builds its top tree and one bottom tree, `2^16` leaves each, before its
/// first signature, so the signers are generated on every available core. The result does
/// not depend on the core count.
pub fn lean_fixture_signers(
    signers: Range<usize>,
    message_index: impl Fn(usize) -> usize + Sync,
) -> Result<Vec<LeanXmssInput>> {
    let count = signers.len();
    let workers = thread::available_parallelism()
        .map_or(1, NonZeroUsize::get)
        .min(count)
        .max(1);
    // Contiguous chunks, joined in order, keep the signers in index order.
    let chunk_len = count.div_ceil(workers).max(1);
    let message_index = &message_index;
    thread::scope(|scope| {
        let workers = signers
            .clone()
            .step_by(chunk_len)
            .map(|start| {
                let chunk = start..(start + chunk_len).min(signers.end);
                scope.spawn(move || {
                    chunk
                        .map(|index| {
                            lean_fixture_signer(index, message_index(index)).with_context(|| {
                                format!("failed to create XMSS fixture signer {index}")
                            })
                        })
                        .collect::<Result<Vec<_>>>()
                })
            })
            .collect::<Vec<_>>();
        let mut inputs = Vec::with_capacity(count);
        for worker in workers {
            let chunk = worker
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic))?;
            inputs.extend(chunk);
        }
        Ok(inputs)
    })
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SampleSummary {
    pub samples_ns: Vec<u64>,
    pub median_ns: u64,
    pub operations_per_second: f64,
}

impl SampleSummary {
    pub fn from_durations(durations: impl IntoIterator<Item = Duration>) -> Result<Self> {
        let samples_ns = durations
            .into_iter()
            .map(|duration| {
                u64::try_from(duration.as_nanos())
                    .context("sample duration exceeds the supported nanosecond range")
            })
            .collect::<Result<Vec<_>>>()?;
        ensure!(!samples_ns.is_empty(), "at least one sample is required");
        ensure!(
            samples_ns.iter().all(|sample| *sample > 0),
            "sample durations must be greater than zero"
        );

        let mut sorted = samples_ns.clone();
        sorted.sort_unstable();
        let midpoint = sorted.len() / 2;
        let median_ns = if sorted.len() % 2 == 0 {
            let lower = sorted[midpoint - 1];
            let upper = sorted[midpoint];
            lower / 2 + upper / 2 + (lower % 2 + upper % 2) / 2
        } else {
            sorted[midpoint]
        };

        Ok(Self {
            samples_ns,
            median_ns,
            operations_per_second: 1_000_000_000.0 / median_ns as f64,
        })
    }

    pub fn ratio_to(&self, baseline: &Self) -> Result<f64> {
        ensure!(
            baseline.median_ns > 0,
            "baseline median must be greater than zero"
        );
        Ok(self.median_ns as f64 / baseline.median_ns as f64)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ComparisonReport {
    pub workload: String,
    pub input_size: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub claim_count: Option<usize>,
    pub lean: SampleSummary,
    pub lighthouse: SampleSummary,
    pub lean_over_lighthouse: f64,
    pub lean_artifact_bytes: usize,
    pub lighthouse_artifact_bytes: usize,
}

impl ComparisonReport {
    pub fn new(
        workload: impl Into<String>,
        input_size: usize,
        lean: SampleSummary,
        lighthouse: SampleSummary,
        lean_artifact_bytes: usize,
        lighthouse_artifact_bytes: usize,
    ) -> Result<Self> {
        let workload = workload.into();
        ensure!(!workload.is_empty(), "workload must not be empty");
        ensure!(input_size > 0, "input size must be greater than zero");
        if workload == KEY_CREATION_WORKLOAD {
            ensure!(
                input_size == 1,
                "{KEY_CREATION_WORKLOAD} must measure exactly one key"
            );
        } else {
            ensure!(
                input_size <= MAX_SIGNERS,
                "input size {input_size} exceeds maximum {MAX_SIGNERS}"
            );
        }
        ensure!(lean.median_ns > 0, "lean median must be greater than zero");
        ensure!(
            lean_artifact_bytes > 0,
            "lean artifact size must be greater than zero"
        );
        ensure!(
            lighthouse_artifact_bytes > 0,
            "Lighthouse artifact size must be greater than zero"
        );
        let lean_over_lighthouse = lean.ratio_to(&lighthouse)?;

        Ok(Self {
            workload,
            input_size,
            claim_count: None,
            lean,
            lighthouse,
            lean_over_lighthouse,
            lean_artifact_bytes,
            lighthouse_artifact_bytes,
        })
    }

    pub fn with_claim_count(mut self, claim_count: usize) -> Result<Self> {
        ensure!(
            self.workload.starts_with("mixed_claim_"),
            "claim count is only valid for mixed-claim workloads"
        );
        ensure!(claim_count > 1, "claim count must be greater than one");
        ensure!(
            claim_count <= self.input_size,
            "claim count must not exceed the signature count"
        );
        ensure!(
            self.input_size.is_multiple_of(claim_count),
            "signature count must be divisible by claim count"
        );
        self.claim_count = Some(claim_count);
        Ok(self)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SupplementalReport {
    pub workload: String,
    pub input_size: usize,
    pub lighthouse: SampleSummary,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct RecursiveAggregationReport {
    pub workload: String,
    pub fan_in: usize,
    pub signers_per_child: usize,
    pub total_signers: usize,
    pub lean: SampleSummary,
    pub lean_artifact_bytes: usize,
}

impl RecursiveAggregationReport {
    pub fn new(
        fan_in: usize,
        signers_per_child: usize,
        lean: SampleSummary,
        lean_artifact_bytes: usize,
    ) -> Result<Self> {
        ensure!(fan_in >= 2, "recursive fan-in must be at least two");
        ensure!(
            fan_in <= MAX_RECURSIVE_FAN_IN,
            "recursive fan-in {fan_in} exceeds maximum {MAX_RECURSIVE_FAN_IN}"
        );
        ensure!(
            signers_per_child == RECURSIVE_CHILD_SIGNERS,
            "recursive child signer count must be exactly {RECURSIVE_CHILD_SIGNERS}"
        );
        let total_signers = fan_in
            .checked_mul(signers_per_child)
            .context("recursive total signer count overflowed")?;
        ensure!(
            lean.median_ns > 0,
            "LeanVM median must be greater than zero"
        );
        ensure!(
            lean_artifact_bytes > 0,
            "LeanVM artifact size must be greater than zero"
        );
        Ok(Self {
            workload: RECURSIVE_AGGREGATION_WORKLOAD.to_owned(),
            fan_in,
            signers_per_child,
            total_signers,
            lean,
            lean_artifact_bytes,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct BenchmarkReport {
    pub lighthouse_revision: String,
    pub samples: usize,
    pub proof_warmup: bool,
    pub comparisons: Vec<ComparisonReport>,
    #[serde(default)]
    pub recursive_aggregations: Vec<RecursiveAggregationReport>,
    pub supplemental: Vec<SupplementalReport>,
}

/// One entry in github-action-benchmark's `customSmallerIsBetter` schema.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct ActionBenchmark {
    pub name: String,
    pub unit: String,
    pub value: f64,
    pub extra: String,
}

impl BenchmarkReport {
    #[must_use]
    pub fn to_table(&self) -> String {
        let mut rows = vec![
            "Workload | Size | Lean median | Lighthouse median | Lean/BLS | Lean ops/s | Lighthouse ops/s | Lean bytes | Lighthouse bytes".to_owned(),
            "--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---:".to_owned(),
        ];

        for comparison in &self.comparisons {
            let input = comparison.claim_count.map_or_else(
                || comparison.input_size.to_string(),
                |claim_count| {
                    format!(
                        "{} signatures / {claim_count} claims",
                        comparison.input_size
                    )
                },
            );
            rows.push(format!(
                "{} | {} | {} | {} | {:.2}x | {:.2} ops/s | {:.2} ops/s | {} | {}",
                comparison.workload,
                input,
                format_duration_ns(comparison.lean.median_ns),
                format_duration_ns(comparison.lighthouse.median_ns),
                comparison.lean_over_lighthouse,
                comparison.lean.operations_per_second,
                comparison.lighthouse.operations_per_second,
                comparison.lean_artifact_bytes,
                comparison.lighthouse_artifact_bytes,
            ));
        }

        for supplemental in &self.supplemental {
            rows.push(format!(
                "{} (Lighthouse-only) | {} | - | {} | - | - | {:.2} ops/s | - | -",
                supplemental.workload,
                supplemental.input_size,
                format_duration_ns(supplemental.lighthouse.median_ns),
                supplemental.lighthouse.operations_per_second,
            ));
        }

        for recursive in &self.recursive_aggregations {
            rows.push(format!(
                "{} (LeanVM-only) | {} proofs x {} signers ({} total) | {} | - | - | {:.2} ops/s | - | {} | -",
                recursive.workload,
                recursive.fan_in,
                recursive.signers_per_child,
                recursive.total_signers,
                format_duration_ns(recursive.lean.median_ns),
                recursive.lean.operations_per_second,
                recursive.lean_artifact_bytes,
            ));
        }

        rows.join("\n")
    }

    pub fn to_action_benchmarks(&self) -> Result<Vec<ActionBenchmark>> {
        ensure!(
            !self.comparisons.is_empty()
                || !self.recursive_aggregations.is_empty()
                || !self.supplemental.is_empty(),
            "cannot export an empty benchmark report"
        );

        let warmup = if self.proof_warmup {
            "enabled"
        } else {
            "disabled"
        };
        let extra = format!(
            "samples={}; proof_warmup={warmup}; lighthouse_revision={}",
            self.samples, self.lighthouse_revision
        );
        let mut entries = Vec::with_capacity(
            self.comparisons.len() * 5
                + self.recursive_aggregations.len() * 2
                + self.supplemental.len(),
        );

        for comparison in &self.comparisons {
            let prefix = comparison.claim_count.map_or_else(
                || format!("{}/size-{}", comparison.workload, comparison.input_size),
                |claim_count| {
                    format!(
                        "{}/signatures-{}/claims-{claim_count}",
                        comparison.workload, comparison.input_size
                    )
                },
            );
            entries.extend([
                action_entry(
                    format!("{prefix}/lean/median"),
                    "ns",
                    comparison.lean.median_ns as f64,
                    &extra,
                ),
                action_entry(
                    format!("{prefix}/lighthouse/median"),
                    "ns",
                    comparison.lighthouse.median_ns as f64,
                    &extra,
                ),
                action_entry(
                    format!("{prefix}/lean-over-lighthouse"),
                    "ratio",
                    comparison.lean_over_lighthouse,
                    &extra,
                ),
                action_entry(
                    format!("{prefix}/lean/artifact"),
                    "bytes",
                    comparison.lean_artifact_bytes as f64,
                    &extra,
                ),
                action_entry(
                    format!("{prefix}/lighthouse/artifact"),
                    "bytes",
                    comparison.lighthouse_artifact_bytes as f64,
                    &extra,
                ),
            ]);
        }

        for recursive in &self.recursive_aggregations {
            let prefix = format!(
                "{}/fan-in-{}/child-signers-{}",
                recursive.workload, recursive.fan_in, recursive.signers_per_child
            );
            entries.extend([
                action_entry(
                    format!("{prefix}/lean/median"),
                    "ns",
                    recursive.lean.median_ns as f64,
                    &extra,
                ),
                action_entry(
                    format!("{prefix}/lean/artifact"),
                    "bytes",
                    recursive.lean_artifact_bytes as f64,
                    &extra,
                ),
            ]);
        }

        for supplemental in &self.supplemental {
            entries.push(action_entry(
                format!(
                    "{}/size-{}/lighthouse/median",
                    supplemental.workload, supplemental.input_size
                ),
                "ns",
                supplemental.lighthouse.median_ns as f64,
                &extra,
            ));
        }

        Ok(entries)
    }
}

fn action_entry(name: String, unit: &str, value: f64, extra: &str) -> ActionBenchmark {
    ActionBenchmark {
        name,
        unit: unit.to_owned(),
        value,
        extra: extra.to_owned(),
    }
}

fn format_duration_ns(nanoseconds: u64) -> String {
    match nanoseconds {
        0..=999 => format!("{nanoseconds} ns"),
        1_000..=999_999 => format!("{:.3} us", nanoseconds as f64 / 1_000.0),
        1_000_000..=999_999_999 => {
            format!("{:.3} ms", nanoseconds as f64 / 1_000_000.0)
        }
        _ => format!("{:.3} s", nanoseconds as f64 / 1_000_000_000.0),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunConfig {
    pub samples: usize,
    pub same_sizes: Vec<usize>,
    pub distinct_sizes: Vec<usize>,
    pub mixed_claim_counts: Vec<usize>,
    pub recursive_fan_ins: Vec<usize>,
    pub json_path: Option<PathBuf>,
    pub action_json_path: Option<PathBuf>,
    pub warmup_proofs: bool,
}

impl RunConfig {
    pub fn parse_from<I, T>(arguments: I) -> Result<Self>
    where
        I: IntoIterator<Item = T>,
        T: Into<OsString>,
    {
        let mut arguments = arguments.into_iter().map(Into::into);
        arguments.next().context("missing program name")?;

        let mut samples = None;
        let mut sizes = None;
        let mut same_sizes = None;
        let mut distinct_sizes = None;
        let mut mixed_claim_counts = None;
        let mut recursive_fan_ins = None;
        let mut json_path = None;
        let mut action_json_path = None;
        let mut warmup_proofs = false;

        while let Some(argument) = arguments.next() {
            match argument.as_os_str() {
                argument if argument == OsStr::new("--samples") => {
                    ensure!(samples.is_none(), "--samples may only be supplied once");
                    let value = option_value("--samples", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--samples value must be valid UTF-8")?;
                    let parsed = text
                        .parse::<usize>()
                        .with_context(|| format!("invalid --samples value `{text}`"))?;
                    ensure!(parsed > 0, "--samples must be greater than zero");
                    samples = Some(parsed);
                }
                argument if argument == OsStr::new("--sizes") => {
                    ensure!(sizes.is_none(), "--sizes may only be supplied once");
                    let value = option_value("--sizes", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--sizes value must be valid UTF-8")?;
                    sizes = Some(parse_sizes("--sizes", text, MAX_SIGNERS)?);
                }
                argument if argument == OsStr::new("--same-sizes") => {
                    ensure!(
                        same_sizes.is_none(),
                        "--same-sizes may only be supplied once"
                    );
                    let value = option_value("--same-sizes", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--same-sizes value must be valid UTF-8")?;
                    same_sizes = Some(parse_sizes("--same-sizes", text, MAX_SIGNERS)?);
                }
                argument if argument == OsStr::new("--distinct-sizes") => {
                    ensure!(
                        distinct_sizes.is_none(),
                        "--distinct-sizes may only be supplied once"
                    );
                    let value = option_value("--distinct-sizes", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--distinct-sizes value must be valid UTF-8")?;
                    distinct_sizes = Some(parse_sizes("--distinct-sizes", text, MAX_SIGNERS)?);
                }
                argument if argument == OsStr::new("--mixed-claim-counts") => {
                    ensure!(
                        mixed_claim_counts.is_none(),
                        "--mixed-claim-counts may only be supplied once"
                    );
                    let value = option_value("--mixed-claim-counts", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--mixed-claim-counts value must be valid UTF-8")?;
                    let parsed = parse_sizes("--mixed-claim-counts", text, MIXED_CLAIM_SIGNATURES)?;
                    ensure!(
                        parsed.iter().all(|count| *count > 1),
                        "--mixed-claim-counts entries must be greater than one"
                    );
                    ensure!(
                        parsed
                            .iter()
                            .all(|count| MIXED_CLAIM_SIGNATURES.is_multiple_of(*count)),
                        "--mixed-claim-counts entries must divide {MIXED_CLAIM_SIGNATURES} signatures evenly"
                    );
                    mixed_claim_counts = Some(parsed);
                }
                argument if argument == OsStr::new("--recursive-fan-ins") => {
                    ensure!(
                        recursive_fan_ins.is_none(),
                        "--recursive-fan-ins may only be supplied once"
                    );
                    let value = option_value("--recursive-fan-ins", arguments.next())?;
                    let text = value
                        .to_str()
                        .context("--recursive-fan-ins value must be valid UTF-8")?;
                    let parsed = parse_sizes("--recursive-fan-ins", text, MAX_RECURSIVE_FAN_IN)?;
                    ensure!(
                        parsed.iter().all(|fan_in| *fan_in >= 2),
                        "--recursive-fan-ins entries must be at least two"
                    );
                    recursive_fan_ins = Some(parsed);
                }
                argument if argument == OsStr::new("--json") => {
                    ensure!(json_path.is_none(), "--json may only be supplied once");
                    let value = option_value("--json", arguments.next())?;
                    ensure!(!value.is_empty(), "--json path must not be empty");
                    json_path = Some(PathBuf::from(value));
                }
                argument if argument == OsStr::new("--action-json") => {
                    ensure!(
                        action_json_path.is_none(),
                        "--action-json may only be supplied once"
                    );
                    let value = option_value("--action-json", arguments.next())?;
                    ensure!(!value.is_empty(), "--action-json path must not be empty");
                    action_json_path = Some(PathBuf::from(value));
                }
                argument if argument == OsStr::new("--warmup-proofs") => {
                    ensure!(!warmup_proofs, "--warmup-proofs may only be supplied once");
                    warmup_proofs = true;
                }
                _ => {
                    return Err(anyhow!(
                        "unknown argument `{}`; expected --samples, --sizes, --same-sizes, --distinct-sizes, --mixed-claim-counts, --recursive-fan-ins, --json, --action-json, or --warmup-proofs",
                        argument.to_string_lossy()
                    ));
                }
            }
        }

        if sizes.is_some() {
            ensure!(
                same_sizes.is_none(),
                "--sizes cannot be combined with --same-sizes"
            );
            ensure!(
                distinct_sizes.is_none(),
                "--sizes cannot be combined with --distinct-sizes"
            );
        }

        ensure_distinct_output_paths(json_path.as_deref(), action_json_path.as_deref())?;

        let default_sizes = || vec![1, 8, 16];
        let (same_sizes, distinct_sizes) = if let Some(sizes) = sizes {
            (sizes.clone(), sizes)
        } else {
            (
                same_sizes.unwrap_or_else(default_sizes),
                distinct_sizes.unwrap_or_else(default_sizes),
            )
        };
        Ok(Self {
            samples: samples.unwrap_or(3),
            same_sizes,
            distinct_sizes,
            mixed_claim_counts: mixed_claim_counts.unwrap_or_default(),
            recursive_fan_ins: recursive_fan_ins.unwrap_or_default(),
            json_path,
            action_json_path,
            warmup_proofs,
        })
    }
}

/// Rejects full and action report paths that currently resolve to the same file.
pub fn ensure_distinct_output_paths(
    json_path: Option<&Path>,
    action_json_path: Option<&Path>,
) -> Result<()> {
    if let (Some(json_path), Some(action_json_path)) = (json_path, action_json_path) {
        ensure!(
            !output_paths_collide(json_path, action_json_path)?,
            "--json and --action-json must write to different paths"
        );
    }
    Ok(())
}

fn output_paths_collide(left: &Path, right: &Path) -> Result<bool> {
    let left = lexically_normalize_absolute(left)?;
    let right = lexically_normalize_absolute(right)?;
    if left == right {
        return Ok(true);
    }

    match same_file::is_same_file(&left, &right) {
        Ok(same) => Ok(same),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error).with_context(|| {
            format!(
                "failed to compare output path identity for {} and {}",
                left.display(),
                right.display()
            )
        }),
    }
}

fn lexically_normalize_absolute(path: &Path) -> Result<PathBuf> {
    let absolute = std::path::absolute(path)
        .with_context(|| format!("failed to resolve output path {}", path.display()))?;
    let mut normalized = PathBuf::new();

    for component in absolute.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                // Popping a root or platform prefix returns false and leaves it intact,
                // matching filesystem resolution of an absolute path above its root.
                normalized.pop();
            }
            _ => normalized.push(component.as_os_str()),
        }
    }

    Ok(normalized)
}

fn option_value(option: &str, value: Option<OsString>) -> Result<OsString> {
    let value = value.with_context(|| format!("{option} requires a value"))?;
    ensure!(
        !value.to_string_lossy().starts_with("--"),
        "{option} requires a value"
    );
    Ok(value)
}

fn parse_sizes(option: &str, value: &str, maximum: usize) -> Result<Vec<usize>> {
    ensure!(
        !value.is_empty(),
        "{option} requires a comma-separated list"
    );

    let mut sizes = Vec::new();
    for component in value.split(',') {
        ensure!(
            !component.is_empty(),
            "{option} contains an empty list entry"
        );
        let size = component
            .parse::<usize>()
            .with_context(|| format!("invalid {option} entry `{component}`"))?;
        ensure!(size > 0, "{option} entries must be greater than zero");
        ensure!(
            size <= maximum,
            "{option} entry {size} exceeds maximum {maximum}"
        );
        ensure!(
            !sizes.contains(&size),
            "{option} contains duplicate entry {size}"
        );
        sizes.push(size);
    }

    Ok(sizes)
}

pub struct BlsFixtureSet {
    claim_count: usize,
    messages: Vec<lighthouse_bls::Hash256>,
    keys: Vec<lighthouse_bls::SecretKey>,
    signatures: Vec<lighthouse_bls::Signature>,
    public_keys: Vec<lighthouse_bls::PublicKey>,
}

impl BlsFixtureSet {
    pub fn same_claim(count: usize) -> Result<Self> {
        let fixtures = Self::build(count, 1)?;
        fixtures.validate_raw()?;
        Ok(fixtures)
    }

    pub fn distinct_claims(count: usize) -> Result<Self> {
        let fixtures = Self::build(count, count)?;
        fixtures.validate_raw()?;
        Ok(fixtures)
    }

    pub fn mixed_claims(signature_count: usize, claim_count: usize) -> Result<Self> {
        let fixtures = Self::build(signature_count, claim_count)?;
        fixtures.validate_raw()?;
        Ok(fixtures)
    }

    fn build(count: usize, claim_count: usize) -> Result<Self> {
        ensure!(count > 0, "BLS fixture count must be greater than zero");
        ensure!(claim_count > 0, "BLS claim count must be greater than zero");
        ensure!(
            claim_count <= count,
            "BLS claim count must not exceed the signature count"
        );
        ensure!(
            count.is_multiple_of(claim_count),
            "BLS signature count must be divisible by claim count"
        );

        let mut messages = Vec::with_capacity(count);
        let mut keys = Vec::with_capacity(count);
        let mut signatures = Vec::with_capacity(count);
        let mut public_keys = Vec::with_capacity(count);

        for index in 0..count {
            let message_index = index % claim_count;
            let message = lighthouse_bls::Hash256::from(indexed_bytes(message_index)?);
            let secret = indexed_bytes(index)
                .with_context(|| format!("failed to create BLS secret for signer {index}"))?;
            let key = lighthouse_bls::SecretKey::deserialize(&secret).map_err(|error| {
                anyhow!("failed to deserialize BLS key for signer {index}: {error:?}")
            })?;
            let public_key = key.public_key();
            let signature = key.sign(message);

            messages.push(message);
            keys.push(key);
            signatures.push(signature);
            public_keys.push(public_key);
        }

        Ok(Self {
            claim_count,
            messages,
            keys,
            signatures,
            public_keys,
        })
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    #[must_use]
    pub fn claim_count(&self) -> usize {
        self.claim_count
    }

    #[must_use]
    pub fn messages(&self) -> &[lighthouse_bls::Hash256] {
        &self.messages
    }

    #[must_use]
    pub fn keys(&self) -> &[lighthouse_bls::SecretKey] {
        &self.keys
    }

    #[must_use]
    pub fn signatures(&self) -> &[lighthouse_bls::Signature] {
        &self.signatures
    }

    #[must_use]
    pub fn public_keys(&self) -> &[lighthouse_bls::PublicKey] {
        &self.public_keys
    }

    #[must_use]
    pub fn aggregate(&self) -> lighthouse_bls::AggregateSignature {
        let mut aggregate = lighthouse_bls::AggregateSignature::infinity();
        for signature in &self.signatures {
            aggregate.add_assign(signature);
        }
        aggregate
    }

    #[must_use]
    pub fn verify_same_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> bool {
        let public_keys = self.public_keys.iter().collect::<Vec<_>>();
        aggregate.fast_aggregate_verify(self.messages[0], &public_keys)
    }

    #[must_use]
    pub fn verify_distinct_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> bool {
        let public_keys = self.public_keys.iter().collect::<Vec<_>>();
        aggregate.aggregate_verify(&self.messages, &public_keys)
    }

    pub fn grouped_claim_context(
        &self,
    ) -> Result<(Vec<lighthouse_bls::Hash256>, Vec<lighthouse_bls::PublicKey>)> {
        let mut messages = Vec::with_capacity(self.claim_count);
        let mut public_keys = Vec::with_capacity(self.claim_count);
        for claim_index in 0..self.claim_count {
            let group = self
                .public_keys
                .iter()
                .skip(claim_index)
                .step_by(self.claim_count)
                .cloned()
                .collect::<Vec<_>>();
            let public_key = lighthouse_bls::AggregatePublicKey::aggregate(&group)
                .map_err(|error| anyhow!("failed to aggregate BLS claim {claim_index}: {error:?}"))?
                .to_public_key();
            messages.push(self.messages[claim_index]);
            public_keys.push(public_key);
        }
        Ok((messages, public_keys))
    }

    pub fn verify_grouped_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> Result<bool> {
        let (messages, public_keys) = self.grouped_claim_context()?;
        let public_keys = public_keys.iter().collect::<Vec<_>>();
        Ok(aggregate.aggregate_verify(&messages, &public_keys))
    }

    #[must_use]
    pub fn signature_sets(&self) -> Vec<lighthouse_bls::SignatureSet<'_>> {
        self.signatures
            .iter()
            .zip(&self.public_keys)
            .zip(&self.messages)
            .map(|((signature, public_key), message)| {
                lighthouse_bls::SignatureSet::single_pubkey(
                    signature,
                    Cow::Borrowed(public_key),
                    *message,
                )
            })
            .collect()
    }

    fn validate_raw(&self) -> Result<()> {
        let expected_len = self.len();
        ensure!(
            [
                self.messages.len(),
                self.keys.len(),
                self.signatures.len(),
                self.public_keys.len(),
            ]
            .into_iter()
            .all(|len| len == expected_len),
            "BLS fixture vectors have inconsistent lengths"
        );

        for index in 0..expected_len {
            ensure!(
                self.signatures[index].verify(&self.public_keys[index], self.messages[index]),
                "BLS signature failed validation for signer {index}"
            );
        }

        Ok(())
    }
}

/// One raw leanXMSS aggregation input: a public key, its message, and its signature.
pub type LeanXmssInput = (
    lean_pq::xmss::PublicKey,
    lean_pq::Message,
    lean_pq::xmss::Signature,
);

/// One leanXMSS aggregate claim: a public key and the message it signed.
pub type LeanXmssClaim = (lean_pq::xmss::PublicKey, lean_pq::Message);

pub struct FixtureSet {
    lean_messages: Vec<lean_pq::Message>,
    lean_signatures: Vec<lean_pq::xmss::Signature>,
    lean_public_keys: Vec<lean_pq::xmss::PublicKey>,
    bls: BlsFixtureSet,
}

impl FixtureSet {
    pub fn same_claim(count: usize) -> Result<Self> {
        Self::build(count, 1)
    }

    pub fn distinct_claims(count: usize) -> Result<Self> {
        Self::build(count, count)
    }

    pub fn mixed_claims(signature_count: usize, claim_count: usize) -> Result<Self> {
        Self::build(signature_count, claim_count)
    }

    fn build(count: usize, claim_count: usize) -> Result<Self> {
        ensure!(
            count <= MAX_SIGNERS,
            "fixture signer count {count} exceeds maximum {MAX_SIGNERS}"
        );
        let bls = BlsFixtureSet::build(count, claim_count)?;

        let mut lean_messages = Vec::with_capacity(count);
        let mut lean_signatures = Vec::with_capacity(count);
        let mut lean_public_keys = Vec::with_capacity(count);

        for (public_key, message, signature) in
            lean_fixture_signers(0..count, |index| index % claim_count)?
        {
            lean_messages.push(message);
            lean_signatures.push(signature);
            lean_public_keys.push(public_key);
        }

        let fixtures = Self {
            lean_messages,
            lean_signatures,
            lean_public_keys,
            bls,
        };
        fixtures.validate_raw()?;
        Ok(fixtures)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.lean_signatures.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lean_signatures.is_empty()
    }

    #[must_use]
    pub fn claim_count(&self) -> usize {
        self.bls.claim_count()
    }

    /// The raw signatures in the shape `lean_pq::aggregate` takes.
    #[must_use]
    pub fn lean_inputs(&self) -> Vec<LeanXmssInput> {
        self.lean_public_keys
            .iter()
            .zip(&self.lean_messages)
            .zip(&self.lean_signatures)
            .map(|((public_key, message), signature)| (*public_key, *message, signature.clone()))
            .collect()
    }

    /// The claims an aggregate of every fixture signature must list, strictly sorted.
    #[must_use]
    pub fn lean_expected_claims(&self) -> Vec<LeanXmssClaim> {
        let mut claims = self
            .lean_public_keys
            .iter()
            .copied()
            .zip(self.lean_messages.iter().copied())
            .collect::<Vec<_>>();
        claims.sort_unstable();
        claims
    }

    #[must_use]
    pub fn lean_messages(&self) -> &[lean_pq::Message] {
        &self.lean_messages
    }

    #[must_use]
    pub fn lean_signatures(&self) -> &[lean_pq::xmss::Signature] {
        &self.lean_signatures
    }

    #[must_use]
    pub fn lean_public_keys(&self) -> &[lean_pq::xmss::PublicKey] {
        &self.lean_public_keys
    }

    #[must_use]
    pub fn bls_messages(&self) -> &[lighthouse_bls::Hash256] {
        self.bls.messages()
    }

    #[must_use]
    pub fn bls_keys(&self) -> &[lighthouse_bls::SecretKey] {
        self.bls.keys()
    }

    #[must_use]
    pub fn bls_signatures(&self) -> &[lighthouse_bls::Signature] {
        self.bls.signatures()
    }

    #[must_use]
    pub fn bls_public_keys(&self) -> &[lighthouse_bls::PublicKey] {
        self.bls.public_keys()
    }

    #[must_use]
    pub fn bls_aggregate(&self) -> lighthouse_bls::AggregateSignature {
        self.bls.aggregate()
    }

    #[must_use]
    pub fn verify_bls_same_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> bool {
        self.bls.verify_same_claim_aggregate(aggregate)
    }

    #[must_use]
    pub fn verify_bls_distinct_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> bool {
        self.bls.verify_distinct_claim_aggregate(aggregate)
    }

    pub fn bls_grouped_claim_context(
        &self,
    ) -> Result<(Vec<lighthouse_bls::Hash256>, Vec<lighthouse_bls::PublicKey>)> {
        self.bls.grouped_claim_context()
    }

    pub fn verify_bls_grouped_claim_aggregate(
        &self,
        aggregate: &lighthouse_bls::AggregateSignature,
    ) -> Result<bool> {
        self.bls.verify_grouped_claim_aggregate(aggregate)
    }

    #[must_use]
    pub fn bls_signature_sets(&self) -> Vec<lighthouse_bls::SignatureSet<'_>> {
        self.bls.signature_sets()
    }

    pub fn validate_raw(&self) -> Result<()> {
        let expected_len = self.len();
        ensure!(
            [
                self.lean_messages.len(),
                self.lean_signatures.len(),
                self.lean_public_keys.len(),
                self.bls.len(),
            ]
            .into_iter()
            .all(|len| len == expected_len),
            "fixture vectors have inconsistent lengths"
        );

        for index in 0..expected_len {
            self.lean_public_keys[index]
                .verify(&self.lean_messages[index], &self.lean_signatures[index])
                .with_context(|| format!("XMSS signature failed validation for signer {index}"))?;
        }

        self.bls.validate_raw()?;

        Ok(())
    }
}

fn indexed_bytes(index: usize) -> Result<[u8; 32]> {
    let value = u64::try_from(index)
        .ok()
        .and_then(|index| index.checked_add(1))
        .with_context(|| format!("signer index {index} cannot be encoded as index + 1"))?;
    let mut bytes = [0; 32];
    bytes[24..].copy_from_slice(&value.to_be_bytes());
    Ok(bytes)
}

/// A leanXMSS seed of `domain`, binding the message index and the key index.
fn lean_seed(
    domain: u8,
    message_index: usize,
    index: usize,
) -> Result<[u8; lean_pq::xmss::SEED_LEN]> {
    let mut seed = indexed_bytes(index)?;
    seed[0] = domain;
    seed[8..16].copy_from_slice(&u64::try_from(message_index)?.to_be_bytes());
    Ok(seed)
}
