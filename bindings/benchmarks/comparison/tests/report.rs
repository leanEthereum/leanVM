use std::time::Duration;

#[cfg(unix)]
use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use lean_pq_comparison::{
    BenchmarkReport, ComparisonReport, RecursiveAggregationReport, RunConfig, SampleSummary,
    SupplementalReport, KEY_CREATION_WORKLOAD, LIGHTHOUSE_REVISION, MAX_RECURSIVE_FAN_IN,
    MAX_SIGNERS, MIXED_CLAIM_COUNTS, MIXED_CLAIM_SIGNATURES, RECURSIVE_CHILD_SIGNERS,
};

#[test]
fn summary_reports_samples_median_and_throughput() {
    let summary = SampleSummary::from_durations([
        Duration::from_millis(30),
        Duration::from_millis(10),
        Duration::from_millis(20),
    ])
    .unwrap();

    assert_eq!(summary.samples_ns, vec![30_000_000, 10_000_000, 20_000_000]);
    assert_eq!(summary.median_ns, 20_000_000);
    assert_eq!(summary.operations_per_second, 50.0);
}

#[test]
fn summary_rejects_empty_zero_and_oversized_durations() {
    assert!(SampleSummary::from_durations([]).is_err());
    assert!(SampleSummary::from_durations([Duration::ZERO]).is_err());
    assert!(SampleSummary::from_durations([Duration::MAX]).is_err());
}

#[test]
fn summary_ratio_uses_integer_medians() {
    let lean = SampleSummary::from_durations([Duration::from_millis(30)]).unwrap();
    let lighthouse = SampleSummary::from_durations([Duration::from_millis(10)]).unwrap();

    assert_eq!(lean.ratio_to(&lighthouse).unwrap(), 3.0);
}

#[test]
fn comparison_report_calculates_ratio_from_medians() {
    let lean = SampleSummary::from_durations([Duration::from_millis(30)]).unwrap();
    let lighthouse = SampleSummary::from_durations([Duration::from_millis(10)]).unwrap();

    let report =
        ComparisonReport::new("same_claim_aggregate", 8, lean, lighthouse, 1_024, 96).unwrap();

    assert_eq!(report.lean_over_lighthouse, 3.0);
}

#[test]
fn comparison_report_accepts_the_expanded_same_claim_limit() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    assert!(ComparisonReport::new(
        "same_claim_aggregate",
        MAX_SIGNERS,
        summary.clone(),
        summary,
        1,
        1,
    )
    .is_ok());
}

#[test]
fn comparison_report_records_a_mixed_claim_shape() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    let report = ComparisonReport::new(
        "mixed_claim_aggregate",
        MIXED_CLAIM_SIGNATURES,
        summary.clone(),
        summary,
        1,
        1,
    )
    .unwrap()
    .with_claim_count(MIXED_CLAIM_COUNTS[1])
    .unwrap();

    assert_eq!(report.input_size, 512);
    assert_eq!(report.claim_count, Some(16));
    assert!(serde_json::to_string(&report)
        .unwrap()
        .contains("\"claim_count\":16"));
}

#[test]
fn comparison_report_rejects_invalid_mixed_claim_shapes() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();
    let report = || {
        ComparisonReport::new(
            "mixed_claim_aggregate",
            8,
            summary.clone(),
            summary.clone(),
            1,
            1,
        )
        .unwrap()
    };

    assert!(report().with_claim_count(1).is_err());
    assert!(report().with_claim_count(3).is_err());
    assert!(report().with_claim_count(16).is_err());
}

#[test]
fn comparison_report_accepts_more_than_sixteen_mixed_claims() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    let report = ComparisonReport::new(
        "mixed_claim_aggregate",
        MIXED_CLAIM_SIGNATURES,
        summary.clone(),
        summary,
        1,
        1,
    )
    .unwrap()
    .with_claim_count(32)
    .unwrap();

    assert_eq!(report.claim_count, Some(32));
}

#[test]
fn comparison_report_accepts_only_one_key_for_key_creation() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    assert!(ComparisonReport::new(
        KEY_CREATION_WORKLOAD,
        1,
        summary.clone(),
        summary.clone(),
        32,
        32,
    )
    .is_ok());
    assert!(
        ComparisonReport::new(KEY_CREATION_WORKLOAD, 2, summary.clone(), summary, 32, 32,).is_err()
    );
}

#[test]
fn comparison_report_rejects_zero_lighthouse_median() {
    let lean = SampleSummary::from_durations([Duration::from_millis(30)]).unwrap();
    let lighthouse = SampleSummary {
        samples_ns: vec![0],
        median_ns: 0,
        operations_per_second: f64::INFINITY,
    };

    assert!(
        ComparisonReport::new("same_claim_aggregate", 8, lean, lighthouse, 1_024, 96,).is_err()
    );
}

#[test]
fn comparison_report_rejects_zero_sizes() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    assert!(ComparisonReport::new(
        "same_claim_aggregate",
        0,
        summary.clone(),
        summary.clone(),
        1,
        1,
    )
    .is_err());
    assert!(ComparisonReport::new(
        "same_claim_aggregate",
        MAX_SIGNERS + 1,
        summary.clone(),
        summary.clone(),
        1,
        1,
    )
    .is_err());
    assert!(ComparisonReport::new(
        "same_claim_aggregate",
        1,
        summary.clone(),
        summary.clone(),
        0,
        1,
    )
    .is_err());
    assert!(
        ComparisonReport::new("same_claim_aggregate", 1, summary.clone(), summary, 1, 0,).is_err()
    );
}

#[test]
fn recursive_report_records_the_fan_in_and_total_signers() {
    let summary = SampleSummary::from_durations([Duration::from_millis(800)]).unwrap();
    let report =
        RecursiveAggregationReport::new(4, RECURSIVE_CHILD_SIGNERS, summary, 250_000).unwrap();

    assert_eq!(report.workload, "recursive_same_claim_aggregate");
    assert_eq!(report.fan_in, 4);
    assert_eq!(report.signers_per_child, 512);
    assert_eq!(report.total_signers, 2_048);
    assert_eq!(report.lean_artifact_bytes, 250_000);
}

#[test]
fn recursive_report_rejects_invalid_shapes() {
    let summary = SampleSummary::from_durations([Duration::from_millis(1)]).unwrap();

    assert!(RecursiveAggregationReport::new(1, 512, summary.clone(), 1).is_err());
    assert!(
        RecursiveAggregationReport::new(MAX_RECURSIVE_FAN_IN + 1, 512, summary.clone(), 1,)
            .is_err()
    );
    assert!(RecursiveAggregationReport::new(2, 0, summary.clone(), 1).is_err());
    assert!(RecursiveAggregationReport::new(2, 511, summary.clone(), 1).is_err());
    assert!(RecursiveAggregationReport::new(2, 512, summary, 0).is_err());
}

#[test]
fn config_defaults_to_practical_sizes_and_three_samples() {
    let config = RunConfig::parse_from(["slow-comparison"]).unwrap();

    assert_eq!(config.samples, 3);
    assert_eq!(config.same_sizes, vec![1, 8, 16]);
    assert_eq!(config.distinct_sizes, vec![1, 8, 16]);
    assert!(config.mixed_claim_counts.is_empty());
    assert!(config.recursive_fan_ins.is_empty());
    assert!(!config.warmup_proofs);
}

#[test]
fn config_accepts_mixed_claim_counts() {
    let config =
        RunConfig::parse_from(["slow-comparison", "--mixed-claim-counts", "8,16"]).unwrap();

    assert_eq!(config.mixed_claim_counts, vec![8, 16]);
    let wide =
        RunConfig::parse_from(["slow-comparison", "--mixed-claim-counts", "32,512"]).unwrap();
    assert_eq!(wide.mixed_claim_counts, vec![32, 512]);
    assert!(RunConfig::parse_from(["slow-comparison", "--mixed-claim-counts", "1024"]).is_err());
    assert!(RunConfig::parse_from([
        "slow-comparison",
        "--mixed-claim-counts",
        "8",
        "--mixed-claim-counts",
        "16",
    ])
    .is_err());
    assert!(RunConfig::parse_from(["slow-comparison", "--mixed-claim-counts", "1,16",]).is_err());
    assert!(RunConfig::parse_from(["slow-comparison", "--mixed-claim-counts", "3,16",]).is_err());
}

#[test]
fn config_accepts_recursive_fan_ins() {
    let config =
        RunConfig::parse_from(["slow-comparison", "--recursive-fan-ins", "2,4,8,16"]).unwrap();

    assert_eq!(config.recursive_fan_ins, vec![2, 4, 8, 16]);
    for invalid in ["1", "17", "2,2"] {
        assert!(
            RunConfig::parse_from(["slow-comparison", "--recursive-fan-ins", invalid,]).is_err()
        );
    }
}

#[test]
fn config_accepts_samples_sizes_and_json_path() {
    let config = RunConfig::parse_from([
        "slow-comparison",
        "--samples",
        "2",
        "--sizes",
        "1,8",
        "--json",
        "/tmp/report.json",
        "--warmup-proofs",
    ])
    .unwrap();

    assert_eq!(config.samples, 2);
    assert_eq!(config.same_sizes, vec![1, 8]);
    assert_eq!(config.distinct_sizes, vec![1, 8]);
    assert_eq!(config.json_path.unwrap().to_str(), Some("/tmp/report.json"));
    assert!(config.action_json_path.is_none());
    assert!(config.warmup_proofs);
}

#[test]
fn config_accepts_action_json_path() {
    let config = RunConfig::parse_from([
        "slow-comparison",
        "--action-json",
        "/tmp/action-report.json",
    ])
    .unwrap();

    assert_eq!(
        config.action_json_path.unwrap().to_str(),
        Some("/tmp/action-report.json")
    );
}

#[test]
fn config_rejects_repeated_missing_and_empty_action_json_paths() {
    for arguments in [
        vec![
            "slow-comparison",
            "--action-json",
            "/tmp/one.json",
            "--action-json",
            "/tmp/two.json",
        ],
        vec!["slow-comparison", "--action-json"],
        vec!["slow-comparison", "--action-json", ""],
    ] {
        assert!(RunConfig::parse_from(arguments).is_err());
    }
}

#[test]
fn config_rejects_colliding_full_and_action_json_paths() {
    let error = RunConfig::parse_from([
        "slow-comparison",
        "--json",
        "/tmp/report.json",
        "--action-json",
        "/tmp/report.json",
    ])
    .unwrap_err();

    assert_eq!(
        error.to_string(),
        "--json and --action-json must write to different paths"
    );
}

#[test]
fn config_rejects_lexically_equivalent_output_paths() {
    for (full, action) in [
        ("/dev/null", "/dev/../dev/null"),
        ("target/report.json", "target/../target/report.json"),
    ] {
        let error =
            RunConfig::parse_from(["slow-comparison", "--json", full, "--action-json", action])
                .unwrap_err();

        assert_eq!(
            error.to_string(),
            "--json and --action-json must write to different paths"
        );
    }
}

#[test]
fn config_accepts_distinct_nonexistent_output_paths() {
    let config = RunConfig::parse_from([
        "slow-comparison",
        "--json",
        "reports/full.json",
        "--action-json",
        "reports/action.json",
    ])
    .unwrap();

    assert_eq!(
        config.json_path.unwrap().to_str(),
        Some("reports/full.json")
    );
    assert_eq!(
        config.action_json_path.unwrap().to_str(),
        Some("reports/action.json")
    );
}

#[cfg(unix)]
#[test]
fn config_rejects_existing_symlink_output_aliases() {
    use std::os::unix::fs::symlink;

    let directory = TestDirectory::new("symlink");
    let full = directory.path().join("full.json");
    let action = directory.path().join("action.json");
    fs::write(&full, "existing report").unwrap();
    symlink(&full, &action).unwrap();

    assert_output_path_collision(&full, &action);
}

#[cfg(unix)]
#[test]
fn config_rejects_existing_hard_link_output_aliases() {
    let directory = TestDirectory::new("hard-link");
    let full = directory.path().join("full.json");
    let action = directory.path().join("action.json");
    fs::write(&full, "existing report").unwrap();
    fs::hard_link(&full, &action).unwrap();

    assert_output_path_collision(&full, &action);
}

#[cfg(unix)]
fn assert_output_path_collision(full: &Path, action: &Path) {
    let result = RunConfig::parse_from([
        OsString::from("slow-comparison"),
        OsString::from("--json"),
        full.as_os_str().to_owned(),
        OsString::from("--action-json"),
        action.as_os_str().to_owned(),
    ]);

    assert_eq!(
        result.unwrap_err().to_string(),
        "--json and --action-json must write to different paths"
    );
}

#[cfg(unix)]
struct TestDirectory(PathBuf);

#[cfg(unix)]
impl TestDirectory {
    fn new(label: &str) -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "lean-pq-comparison-{label}-{}-{id}",
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

#[test]
fn config_accepts_independent_same_and_distinct_sizes() {
    let config = RunConfig::parse_from([
        "slow-comparison",
        "--same-sizes",
        "32,64,128,256,512",
        "--distinct-sizes",
        "1,8,16",
    ])
    .unwrap();

    assert_eq!(config.same_sizes, vec![32, 64, 128, 256, 512]);
    assert_eq!(config.distinct_sizes, vec![1, 8, 16]);
}

#[test]
fn config_defaults_the_size_axis_that_is_not_overridden() {
    let same_only = RunConfig::parse_from(["slow-comparison", "--same-sizes", "32,512"]).unwrap();
    assert_eq!(same_only.same_sizes, vec![32, 512]);
    assert_eq!(same_only.distinct_sizes, vec![1, 8, 16]);

    let distinct_only =
        RunConfig::parse_from(["slow-comparison", "--distinct-sizes", "1,8"]).unwrap();
    assert_eq!(distinct_only.same_sizes, vec![1, 8, 16]);
    assert_eq!(distinct_only.distinct_sizes, vec![1, 8]);
}

#[test]
fn config_rejects_sizes_shorthand_with_specific_size_options() {
    let same_error =
        RunConfig::parse_from(["slow-comparison", "--sizes", "1,8", "--same-sizes", "32,64"])
            .unwrap_err();
    assert_eq!(
        same_error.to_string(),
        "--sizes cannot be combined with --same-sizes"
    );

    let distinct_error = RunConfig::parse_from([
        "slow-comparison",
        "--distinct-sizes",
        "1,8",
        "--sizes",
        "1,8",
    ])
    .unwrap_err();
    assert_eq!(
        distinct_error.to_string(),
        "--sizes cannot be combined with --distinct-sizes"
    );
}

#[test]
fn config_reports_the_exact_independent_size_limits() {
    let same_error = RunConfig::parse_from(["slow-comparison", "--same-sizes", "513"]).unwrap_err();
    assert_eq!(
        same_error.to_string(),
        "--same-sizes entry 513 exceeds maximum 512"
    );

    let distinct_error =
        RunConfig::parse_from(["slow-comparison", "--distinct-sizes", "513"]).unwrap_err();
    assert_eq!(
        distinct_error.to_string(),
        "--distinct-sizes entry 513 exceeds maximum 512"
    );

    let distinct =
        RunConfig::parse_from(["slow-comparison", "--distinct-sizes", "17,512"]).unwrap();
    assert_eq!(distinct.distinct_sizes, vec![17, 512]);
}

#[test]
fn config_rejects_zero_samples_and_out_of_range_sizes() {
    assert!(RunConfig::parse_from(["slow-comparison", "--samples", "0"]).is_err());
    assert!(RunConfig::parse_from(["slow-comparison", "--sizes", "0"]).is_err());
    assert!(RunConfig::parse_from(["slow-comparison", "--sizes", "513"]).is_err());
}

#[test]
fn config_rejects_unknown_repeated_and_missing_options() {
    for arguments in [
        vec!["slow-comparison", "--unknown"],
        vec!["slow-comparison", "--samples", "2", "--samples", "3"],
        vec!["slow-comparison", "--sizes", "1", "--sizes", "8"],
        vec!["slow-comparison", "--same-sizes", "1", "--same-sizes", "8"],
        vec![
            "slow-comparison",
            "--distinct-sizes",
            "1",
            "--distinct-sizes",
            "8",
        ],
        vec![
            "slow-comparison",
            "--json",
            "/tmp/one.json",
            "--json",
            "/tmp/two.json",
        ],
        vec!["slow-comparison", "--samples"],
        vec!["slow-comparison", "--sizes"],
        vec!["slow-comparison", "--same-sizes"],
        vec!["slow-comparison", "--distinct-sizes"],
        vec!["slow-comparison", "--recursive-fan-ins"],
        vec!["slow-comparison", "--json"],
        vec!["slow-comparison", "--warmup-proofs", "--warmup-proofs"],
    ] {
        assert!(RunConfig::parse_from(arguments).is_err());
    }
}

#[test]
fn unknown_option_error_lists_the_proof_warmup_flag() {
    let error = RunConfig::parse_from(["slow-comparison", "--unknown"]).unwrap_err();

    assert!(error.to_string().contains("--warmup-proofs"));
    assert!(error.to_string().contains("--action-json"));
}

#[test]
fn config_rejects_malformed_and_duplicate_sizes() {
    for sizes in ["", "1,", ",1", "1,,8", "one", "1,1"] {
        assert!(RunConfig::parse_from(["slow-comparison", "--sizes", sizes]).is_err());
        assert!(RunConfig::parse_from(["slow-comparison", "--same-sizes", sizes]).is_err());
        assert!(RunConfig::parse_from(["slow-comparison", "--distinct-sizes", sizes]).is_err());
        assert!(RunConfig::parse_from(["slow-comparison", "--recursive-fan-ins", sizes]).is_err());
    }
}

#[test]
fn benchmark_report_round_trips_through_json() {
    let lean = SampleSummary::from_durations([Duration::from_millis(30)]).unwrap();
    let lighthouse = SampleSummary::from_durations([Duration::from_millis(10)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: "e423a66763bb1bd780492d635123f208d80c3538".to_owned(),
        samples: 1,
        proof_warmup: true,
        comparisons: vec![ComparisonReport::new(
            "distinct_claim_verify_conceptual",
            8,
            lean,
            lighthouse.clone(),
            1_024,
            96,
        )
        .unwrap()],
        recursive_aggregations: vec![RecursiveAggregationReport::new(
            2,
            RECURSIVE_CHILD_SIGNERS,
            SampleSummary::from_durations([Duration::from_millis(800)]).unwrap(),
            250_000,
        )
        .unwrap()],
        supplemental: vec![SupplementalReport {
            workload: "lighthouse_signature_sets_verify".to_owned(),
            input_size: 8,
            lighthouse,
        }],
    };

    let json = serde_json::to_string_pretty(&report).unwrap();
    let restored: BenchmarkReport = serde_json::from_str(&json).unwrap();

    assert_eq!(restored, report);
    assert!(restored.proof_warmup);
    assert!(json.contains("\"workload\": \"distinct_claim_verify_conceptual\""));
    assert!(json.contains("\"workload\": \"lighthouse_signature_sets_verify\""));
    assert!(json.contains("\"workload\": \"recursive_same_claim_aggregate\""));
    assert!(report
        .to_table()
        .contains("distinct_claim_verify_conceptual"));
}

#[test]
fn action_benchmarks_include_exact_paired_and_supplemental_entries() {
    let lean = SampleSummary::from_durations([Duration::from_millis(30)]).unwrap();
    let lighthouse = SampleSummary::from_durations([Duration::from_millis(10)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: LIGHTHOUSE_REVISION.to_owned(),
        samples: 3,
        proof_warmup: true,
        comparisons: vec![ComparisonReport::new(
            "same_claim_aggregate",
            8,
            lean,
            lighthouse.clone(),
            1_024,
            96,
        )
        .unwrap()],
        recursive_aggregations: vec![RecursiveAggregationReport::new(
            2,
            RECURSIVE_CHILD_SIGNERS,
            SampleSummary::from_durations([Duration::from_millis(800)]).unwrap(),
            250_000,
        )
        .unwrap()],
        supplemental: vec![SupplementalReport {
            workload: "lighthouse_signature_sets_verify".to_owned(),
            input_size: 8,
            lighthouse,
        }],
    };

    let entries = report.to_action_benchmarks().unwrap();
    let json = serde_json::to_value(&entries).unwrap();
    let extra =
        format!("samples=3; proof_warmup=enabled; lighthouse_revision={LIGHTHOUSE_REVISION}");

    assert_eq!(
        json,
        serde_json::json!([
            {
                "name": "same_claim_aggregate/size-8/lean/median",
                "unit": "ns",
                "value": 30_000_000.0,
                "extra": extra,
            },
            {
                "name": "same_claim_aggregate/size-8/lighthouse/median",
                "unit": "ns",
                "value": 10_000_000.0,
                "extra": extra,
            },
            {
                "name": "same_claim_aggregate/size-8/lean-over-lighthouse",
                "unit": "ratio",
                "value": 3.0,
                "extra": extra,
            },
            {
                "name": "same_claim_aggregate/size-8/lean/artifact",
                "unit": "bytes",
                "value": 1_024.0,
                "extra": extra,
            },
            {
                "name": "same_claim_aggregate/size-8/lighthouse/artifact",
                "unit": "bytes",
                "value": 96.0,
                "extra": extra,
            },
            {
                "name": "recursive_same_claim_aggregate/fan-in-2/child-signers-512/lean/median",
                "unit": "ns",
                "value": 800_000_000.0,
                "extra": extra,
            },
            {
                "name": "recursive_same_claim_aggregate/fan-in-2/child-signers-512/lean/artifact",
                "unit": "bytes",
                "value": 250_000.0,
                "extra": extra,
            },
            {
                "name": "lighthouse_signature_sets_verify/size-8/lighthouse/median",
                "unit": "ns",
                "value": 10_000_000.0,
                "extra": extra,
            },
        ])
    );
}

#[test]
fn action_benchmark_context_records_disabled_proof_warmup() {
    let lighthouse = SampleSummary::from_durations([Duration::from_micros(500)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: "revision".to_owned(),
        samples: 1,
        proof_warmup: false,
        comparisons: vec![],
        recursive_aggregations: vec![],
        supplemental: vec![SupplementalReport {
            workload: "lighthouse_signature_sets_verify".to_owned(),
            input_size: 1,
            lighthouse,
        }],
    };

    let entries = report.to_action_benchmarks().unwrap();

    assert_eq!(
        entries[0].extra,
        "samples=1; proof_warmup=disabled; lighthouse_revision=revision"
    );
}

#[test]
fn action_benchmarks_reject_an_empty_report() {
    let report = BenchmarkReport {
        lighthouse_revision: LIGHTHOUSE_REVISION.to_owned(),
        samples: 3,
        proof_warmup: true,
        comparisons: vec![],
        recursive_aggregations: vec![],
        supplemental: vec![],
    };

    assert_eq!(
        report.to_action_benchmarks().unwrap_err().to_string(),
        "cannot export an empty benchmark report"
    );
}

#[test]
fn action_export_does_not_change_the_full_report_schema() {
    let lighthouse = SampleSummary::from_durations([Duration::from_micros(500)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: "revision".to_owned(),
        samples: 1,
        proof_warmup: false,
        comparisons: vec![],
        recursive_aggregations: vec![],
        supplemental: vec![SupplementalReport {
            workload: "lighthouse_signature_sets_verify".to_owned(),
            input_size: 1,
            lighthouse,
        }],
    };

    let json = serde_json::to_value(&report).unwrap();
    let keys = json
        .as_object()
        .unwrap()
        .keys()
        .cloned()
        .collect::<Vec<_>>();

    assert_eq!(
        keys,
        vec![
            "comparisons",
            "lighthouse_revision",
            "proof_warmup",
            "recursive_aggregations",
            "samples",
            "supplemental",
        ]
    );
}

#[test]
fn reported_lighthouse_revision_matches_manifest_pin() {
    let manifest = include_str!("../Cargo.toml");
    let expected = format!("rev = \"{LIGHTHOUSE_REVISION}\"");
    let dependency = manifest
        .lines()
        .find(|line| line.starts_with("lighthouse-bls ="))
        .expect("manifest must contain the Lighthouse BLS dependency");

    assert!(dependency.contains(&expected));
}

#[test]
fn table_contains_paired_measurements_and_artifact_sizes() {
    let lean = SampleSummary::from_durations([Duration::from_millis(2)]).unwrap();
    let lighthouse = SampleSummary::from_durations([Duration::from_micros(500)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: "revision".to_owned(),
        samples: 1,
        proof_warmup: false,
        comparisons: vec![ComparisonReport::new(
            "same_claim_aggregate",
            8,
            lean,
            lighthouse,
            1_024,
            96,
        )
        .unwrap()],
        recursive_aggregations: vec![],
        supplemental: vec![],
    };

    let table = report.to_table();

    assert!(table.contains("same_claim_aggregate"));
    assert!(table.contains('8'));
    assert!(table.contains("2.000 ms"));
    assert!(table.contains("500.000 us"));
    assert!(table.contains("4.00x"));
    assert!(table.contains("500.00 ops/s"));
    assert!(table.contains("2000.00 ops/s"));
    assert!(table.contains("1024"));
    assert!(table.contains("96"));
}

#[test]
fn table_visibly_labels_supplemental_rows_as_lighthouse_only() {
    let lighthouse = SampleSummary::from_durations([Duration::from_micros(500)]).unwrap();
    let report = BenchmarkReport {
        lighthouse_revision: "revision".to_owned(),
        samples: 1,
        proof_warmup: false,
        comparisons: vec![],
        recursive_aggregations: vec![],
        supplemental: vec![SupplementalReport {
            workload: "lighthouse_signature_sets_verify".to_owned(),
            input_size: 8,
            lighthouse,
        }],
    };

    let table = report.to_table();

    assert!(table.contains("lighthouse_signature_sets_verify"));
    assert!(table.contains("Lighthouse-only"));
    assert!(table.contains("500.000 us"));
}
