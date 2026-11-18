#!/usr/bin/env python3
"""Normalize benchmark artifacts for the latest-results dashboard."""

from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path


ARTIFACT_SIZE_RE = re.compile(
    r"^artifact-size "
    r"(?P<artifact>public_key|raw_signature)/"
    r"(?P<implementation>lean|lighthouse) (?P<bytes>[1-9]\d*)$"
)
EXPECTED_FAST_ARTIFACTS = {
    (artifact, implementation)
    for artifact in ("public_key", "raw_signature")
    for implementation in ("lean", "lighthouse")
}
PEAK_RSS_RE = re.compile(
    r"^\s*Maximum resident set size \(kbytes\):\s*(?P<value>\S+)\s*$"
)
MAX_EXACT_KIB = (2**53 - 1) // 1024
MAX_RECURSIVE_FAN_IN = 16
RECURSIVE_CHILD_SIGNERS = 512


def parse_environment(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    cpu = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("Model name:"):
            cpu = line.partition(":")[2].strip()
        elif "=" in line:
            key, value = line.split("=", 1)
            values[key.strip()] = value.strip()

    required = ("commit", "measured_at", "suite")
    missing = [key for key in required if not values.get(key)]
    if missing:
        raise ValueError(f"environment is missing: {', '.join(missing)}")
    if not cpu:
        raise ValueError("environment is missing: cpu")
    values["cpu"] = cpu
    return values


def parse_benchmark_name(name: str) -> tuple[str, str, int | None]:
    parts = name.split("/")
    if (
        len(parts) == 3
        and parts[0]
        and parts[1] in {"lean", "lighthouse"}
        and parts[2].isdigit()
    ):
        input_size = int(parts[2])
        if input_size <= 0:
            raise ValueError(f"benchmark input size must be positive: {name}")
        return parts[0], parts[1], input_size

    workload, separator, suffix = name.rpartition("/")
    if not separator:
        raise ValueError(f"unrecognized benchmark name: {name}")

    if suffix in {"lean", "lighthouse"}:
        if not workload:
            raise ValueError(f"unrecognized benchmark name: {name}")
        return workload, suffix, None

    if workload.startswith("lighthouse_") and suffix.isdigit():
        normalized_workload = workload.removeprefix("lighthouse_")
        if not normalized_workload:
            raise ValueError(f"unrecognized benchmark name: {name}")
        input_size = int(suffix)
        if input_size <= 0:
            raise ValueError(f"benchmark input size must be positive: {name}")
        return normalized_workload, "lighthouse", input_size

    raise ValueError(f"unrecognized benchmark name: {name}")


def build_fast(
    input_path: Path,
    criterion_dir: Path,
    environment_path: Path,
    output_path: Path,
) -> None:
    environment = parse_environment(environment_path)
    if environment["suite"] != "fast":
        raise ValueError("environment suite must be fast")

    lines = input_path.read_text(encoding="utf-8").splitlines()
    artifacts = []
    seen_artifacts = set()
    for line in lines:
        match = ARTIFACT_SIZE_RE.fullmatch(line.strip())
        if not match:
            continue
        key = (match.group("artifact"), match.group("implementation"))
        if key in seen_artifacts:
            raise ValueError(f"duplicate artifact size: {'/'.join(key)}")
        seen_artifacts.add(key)
        artifacts.append(
            {
                "artifact": key[0],
                "implementation": key[1],
                "bytes": int(match.group("bytes")),
            }
        )
    if seen_artifacts != EXPECTED_FAST_ARTIFACTS:
        missing = sorted(EXPECTED_FAST_ARTIFACTS - seen_artifacts)
        raise ValueError(f"benchmark output is missing artifact sizes: {missing}")

    benchmarks = []
    seen = set()
    for benchmark_path in sorted(criterion_dir.glob("**/new/benchmark.json")):
        benchmark = json.loads(benchmark_path.read_text(encoding="utf-8"))
        estimates_path = benchmark_path.with_name("estimates.json")
        estimates = json.loads(estimates_path.read_text(encoding="utf-8"))
        name = benchmark.get("full_id")
        if not isinstance(name, str) or not name:
            raise ValueError(f"invalid Criterion benchmark id: {benchmark_path}")
        if name in seen:
            raise ValueError(f"duplicate benchmark: {name}")
        seen.add(name)
        workload, implementation, input_size = parse_benchmark_name(name)
        try:
            median = estimates["median"]["point_estimate"]
            deviation = estimates["std_dev"]["point_estimate"]
        except (KeyError, TypeError) as error:
            raise ValueError(f"invalid Criterion estimates: {estimates_path}") from error
        if not isinstance(median, (int, float)) or not math.isfinite(median):
            raise ValueError(f"invalid Criterion median: {estimates_path}")
        if not isinstance(deviation, (int, float)) or not math.isfinite(deviation):
            raise ValueError(f"invalid Criterion deviation: {estimates_path}")
        median_ns = round(median)
        deviation_ns = round(deviation)
        if median_ns <= 0 or deviation_ns < 0:
            raise ValueError(f"invalid timing for benchmark: {name}")
        benchmarks.append(
            {
                "name": name,
                "workload": workload,
                "implementation": implementation,
                "input_size": input_size,
                "median_ns": median_ns,
                "deviation_ns": deviation_ns,
            }
        )

    if not benchmarks:
        raise ValueError("Criterion output did not contain any benchmark estimates")
    implementations_by_workload: dict[tuple[str, int | None], set[str]] = {}
    for result in benchmarks:
        key = (result["workload"], result["input_size"])
        implementations_by_workload.setdefault(key, set()).add(result["implementation"])
    unpaired = [
        key
        for key, implementations in implementations_by_workload.items()
        if implementations != {"lean", "lighthouse"}
    ]
    if unpaired:
        raise ValueError(f"fast benchmarks are missing paired implementations: {unpaired}")

    document = {
        "schema_version": 1,
        "suite": "fast",
        "measured_at": environment["measured_at"],
        "environment": {
            key: value for key, value in environment.items() if key != "suite"
        },
        "artifacts": artifacts,
        "benchmarks": benchmarks,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")


def positive_integer(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{field} must be a positive integer")
    return value


def positive_number(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be a positive number")
    converted = float(value)
    if not math.isfinite(converted) or converted <= 0:
        raise ValueError(f"{field} must be a positive finite number")
    return converted


def validate_summary(summary: object, field: str, samples: int) -> None:
    if not isinstance(summary, dict):
        raise ValueError(f"{field} must be an object")
    samples_ns = summary.get("samples_ns")
    if not isinstance(samples_ns, list) or len(samples_ns) != samples:
        raise ValueError(f"{field}.samples_ns must contain {samples} samples")
    for index, value in enumerate(samples_ns):
        positive_integer(value, f"{field}.samples_ns[{index}]")
    positive_integer(summary.get("median_ns"), f"{field}.median_ns")
    positive_number(
        summary.get("operations_per_second"), f"{field}.operations_per_second"
    )


def validate_comparison(row: object, samples: int, index: int) -> None:
    field = f"comparisons[{index}]"
    if not isinstance(row, dict):
        raise ValueError(f"{field} must be an object")
    if not isinstance(row.get("workload"), str) or not row["workload"]:
        raise ValueError(f"{field}.workload must be a non-empty string")
    input_size = positive_integer(row.get("input_size"), f"{field}.input_size")
    claim_count = row.get("claim_count")
    is_mixed = row["workload"].startswith("mixed_claim_")
    if is_mixed:
        claim_count = positive_integer(claim_count, f"{field}.claim_count")
        if claim_count > input_size:
            raise ValueError(f"{field}.claim_count must not exceed input_size")
        if input_size % claim_count != 0:
            raise ValueError(f"{field}.input_size must be divisible by claim_count")
    elif claim_count is not None:
        raise ValueError(f"{field}.claim_count is only valid for mixed-claim rows")
    validate_summary(row.get("lean"), f"{field}.lean", samples)
    validate_summary(row.get("lighthouse"), f"{field}.lighthouse", samples)
    positive_number(
        row.get("lean_over_lighthouse"), f"{field}.lean_over_lighthouse"
    )
    positive_integer(row.get("lean_artifact_bytes"), f"{field}.lean_artifact_bytes")
    positive_integer(
        row.get("lighthouse_artifact_bytes"),
        f"{field}.lighthouse_artifact_bytes",
    )


def validate_supplemental(row: object, samples: int, index: int) -> None:
    field = f"supplemental[{index}]"
    if not isinstance(row, dict):
        raise ValueError(f"{field} must be an object")
    if not isinstance(row.get("workload"), str) or not row["workload"]:
        raise ValueError(f"{field}.workload must be a non-empty string")
    positive_integer(row.get("input_size"), f"{field}.input_size")
    validate_summary(row.get("lighthouse"), f"{field}.lighthouse", samples)


def validate_recursive_aggregation(row: object, samples: int, index: int) -> None:
    field = f"recursive_aggregations[{index}]"
    if not isinstance(row, dict):
        raise ValueError(f"{field} must be an object")
    if row.get("workload") != "recursive_same_claim_aggregate":
        raise ValueError(f"{field}.workload must identify recursive same-claim aggregation")
    fan_in = positive_integer(row.get("fan_in"), f"{field}.fan_in")
    if fan_in < 2 or fan_in > MAX_RECURSIVE_FAN_IN:
        raise ValueError(f"{field}.fan_in must be between 2 and {MAX_RECURSIVE_FAN_IN}")
    signers_per_child = positive_integer(
        row.get("signers_per_child"), f"{field}.signers_per_child"
    )
    if signers_per_child != RECURSIVE_CHILD_SIGNERS:
        raise ValueError(
            f"{field}.signers_per_child must be {RECURSIVE_CHILD_SIGNERS}"
        )
    total_signers = positive_integer(row.get("total_signers"), f"{field}.total_signers")
    if total_signers != fan_in * signers_per_child:
        raise ValueError(f"{field}.total_signers does not match its fan-in shape")
    validate_summary(row.get("lean"), f"{field}.lean", samples)
    positive_integer(row.get("lean_artifact_bytes"), f"{field}.lean_artifact_bytes")


def parse_peak_rss(path: Path) -> int:
    values = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = PEAK_RSS_RE.fullmatch(line)
        if match:
            values.append(match.group("value"))
    if len(values) != 1:
        raise ValueError("resource report must contain exactly one peak-RSS measurement")
    if not values[0].isdigit():
        raise ValueError("peak RSS must be a positive integer")
    peak_kib = int(values[0])
    if peak_kib <= 0:
        raise ValueError("peak RSS must be greater than zero")
    if peak_kib > MAX_EXACT_KIB:
        raise ValueError("peak RSS is too large to represent exactly in bytes")
    return peak_kib * 1024


def build_slow(
    input_path: Path,
    resource_path: Path,
    environment_path: Path,
    output_path: Path,
) -> None:
    environment = parse_environment(environment_path)
    if environment["suite"] != "slow":
        raise ValueError("environment suite must be slow")

    report = json.loads(input_path.read_text(encoding="utf-8"))
    if not isinstance(report, dict):
        raise ValueError("slow report must be an object")
    revision = report.get("lighthouse_revision")
    if not isinstance(revision, str) or not revision:
        raise ValueError("lighthouse_revision must be a non-empty string")
    if environment.get("lighthouse_revision") != revision:
        raise ValueError("environment and report Lighthouse revisions differ")
    samples = positive_integer(report.get("samples"), "samples")
    if environment.get("samples") != str(samples):
        raise ValueError("environment and report sample counts differ")
    proof_warmup = report.get("proof_warmup")
    if not isinstance(proof_warmup, bool):
        raise ValueError("proof_warmup must be a boolean")
    expected_warmup = "enabled" if proof_warmup else "disabled"
    if environment.get("proof_warmup") != expected_warmup:
        raise ValueError("environment and report proof-warmup modes differ")

    comparisons = report.get("comparisons")
    recursive_aggregations = report.get("recursive_aggregations", [])
    supplemental = report.get("supplemental")
    if not isinstance(comparisons, list) or not comparisons:
        raise ValueError("comparisons must be a non-empty list")
    if not isinstance(supplemental, list):
        raise ValueError("supplemental must be a list")
    if not isinstance(recursive_aggregations, list):
        raise ValueError("recursive_aggregations must be a list")
    for index, row in enumerate(comparisons):
        validate_comparison(row, samples, index)
    for index, row in enumerate(supplemental):
        validate_supplemental(row, samples, index)
    for index, row in enumerate(recursive_aggregations):
        validate_recursive_aggregation(row, samples, index)
    expected_fan_ins = ",".join(str(row["fan_in"]) for row in recursive_aggregations)
    if environment.get("recursive_fan_ins", "") != expected_fan_ins:
        raise ValueError("environment and report recursive fan-ins differ")
    key_creation = [
        row for row in comparisons if row.get("workload") == "key_creation"
    ]
    if len(key_creation) != 1:
        raise ValueError("comparisons must contain exactly one key_creation row")
    if key_creation[0].get("input_size") != 1:
        raise ValueError("key_creation must measure exactly one key")

    peak_rss_bytes = parse_peak_rss(resource_path)
    document = {
        "schema_version": 1,
        "suite": "slow",
        "measured_at": environment["measured_at"],
        "environment": {
            key: value for key, value in environment.items() if key != "suite"
        },
        "lighthouse_revision": revision,
        "samples": samples,
        "proof_warmup": proof_warmup,
        "peak_rss_bytes": peak_rss_bytes,
        "comparisons": comparisons,
        "recursive_aggregations": recursive_aggregations,
        "supplemental": supplemental,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    print(
        f"Suite peak RSS: {peak_rss_bytes:,} bytes "
        f"({peak_rss_bytes / 1024**3:.2f} GiB)"
    )


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    fast = subparsers.add_parser("fast")
    fast.add_argument("--input", type=Path, required=True)
    fast.add_argument("--criterion-dir", type=Path, required=True)
    fast.add_argument("--environment", type=Path, required=True)
    fast.add_argument("--output", type=Path, required=True)
    slow = subparsers.add_parser("slow")
    slow.add_argument("--input", type=Path, required=True)
    slow.add_argument("--resource", type=Path, required=True)
    slow.add_argument("--environment", type=Path, required=True)
    slow.add_argument("--output", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    if args.command == "fast":
        build_fast(args.input, args.criterion_dir, args.environment, args.output)
    elif args.command == "slow":
        build_slow(args.input, args.resource, args.environment, args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
