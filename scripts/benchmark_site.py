#!/usr/bin/env python3
"""Plan, measure and atomically publish one complete, fresh benchmark snapshot."""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MAX_JSON = 8 * 1024 * 1024
SHA = re.compile(r"[0-9a-f]{40}")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
TESTBEDS = ("x86-64", "arm64")
# Planned only when the workflow has a runner for it (`BENCHMARK_MACOS_RUNNER`).
OPTIONAL_TESTBEDS = ("macos-arm64",)
TESTBED_ARCH = {"x86-64": "x86-64", "arm64": "arm64", "macos-arm64": "arm64"}
PROGRAMS = {
    "fibonacci-asm-2000000": ("Fibonacci", "2,000,000 steps modulo 2^64", "bins/leanvm/src/workload.rs"),
    "hash-50000": ("BLAKE2s guest", "Hash 50,000 bytes through the precompile", "programs/hash/guest/src/main.rs"),
    "leanxmss-100": ("leanXMSS", "Verify 100 signatures", "programs/leanxmss/guest/src/main.rs"),
    "leansphincs-26": ("leanSPHINCS", "Verify 26 signatures", "programs/leansphincs/guest/src/main.rs"),
    "leanda-1": ("leanDA", "Check 1 blob of 128 KiB and compute its commitment", "programs/leanda/guest/src/main.rs"),
}
_SPEC = importlib.util.spec_from_file_location("mobile_report", Path(__file__).with_name("mobile-bench-report.py"))
mobile_report = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mobile_report)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def positive(value):
    require(type(value) in (int, float) and math.isfinite(value) and value > 0, "invalid positive measurement")
    return value


def integer(value, maximum=None):
    require(type(value) is int and value > 0 and (maximum is None or value <= maximum), "invalid positive integer")
    return value


def text(value):
    require(isinstance(value, str) and 0 < len(value) <= 500, "invalid text")
    return value


def instant(value):
    require(isinstance(value, str), "missing timestamp")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(parsed.tzinfo is not None and parsed.utcoffset().total_seconds() == 0, "timestamp must be UTC")
    return parsed


def now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def decode(data):
    require(len(data) <= MAX_JSON, "JSON too large")
    return json.loads(data, object_pairs_hook=unique_object)


def load(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), f"missing or unsafe file: {path}")
    require(path.stat().st_size <= MAX_JSON, "JSON too large")
    return decode(path.read_text())


def atomic_write(path, document, immutable=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, prefix=f".{path.name}.", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(document, stream, indent=2, allow_nan=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        if immutable:
            os.link(temporary, path)  # Atomic create, never replace an existing plan.
        else:
            os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def expected_benchmarks():
    names = {f"{name}-16thread" for name in PROGRAMS}
    names.update(f"leanxmss-100-{count}thread" for count in (1, 4, 8))
    names.update(f"aggregate-leanxmss-100-{arity}to1{suffix}"
                 for arity in (2, 4) for suffix in ("-16thread", "-1thread", "-4thread", "-8thread"))
    return sorted(names)


def expected_results(benchmark):
    return [benchmark + "-first", benchmark + "-node"] if benchmark.startswith("aggregate-") else [benchmark]


def workload(name):
    threads = re.search(r"-(\d+)thread(?:-|$)", name)
    count = int(threads[1]) if threads else None
    clean = re.sub(r"-\d+thread", "", name)
    if clean in PROGRAMS:
        return (*PROGRAMS[clean], "program", count)
    tree = re.fullmatch(r"aggregate-leanxmss-100-(2|4)to1-(first|node)", clean)
    if tree:
        arity, level = tree.groups()
        description = (f"{arity} to 1, first-level node over {arity} copies of a 100-signature leaf proof"
                       if level == "first" else
                       f"{arity} to 1, higher node over {arity} tree proofs; 100-signature leaves")
        return "leanXMSS aggregation", description, "crates/leanvm_core/src/rec/tree/mod.rs", "aggregation", count
    return None


def provenance(repository, commit, run_id):
    return {"repository": repository, "branch": "riscv-exploration", "commit": commit,
            "run_id": run_id, "run_url": f"https://github.com/{repository}/actions/runs/{run_id}"}


def validate_source(source):
    require(set(source) == {"repository", "branch", "commit", "run_id", "run_url"}, "invalid snapshot provenance")
    require(isinstance(source["repository"], str) and REPOSITORY.fullmatch(source["repository"]), "invalid repository")
    require(isinstance(source["commit"], str) and SHA.fullmatch(source["commit"]), "invalid commit")
    integer(source["run_id"])
    require(source == provenance(source["repository"], source["commit"], source["run_id"]), "invalid snapshot provenance")


def planned_testbeds(optional=()):
    require(set(optional) <= set(OPTIONAL_TESTBEDS), "unknown optional testbed")
    return [*TESTBEDS, *(name for name in OPTIONAL_TESTBEDS if name in optional)]


def make_plan(repository, commit, run_id, rounds=5, optional=()):
    plan = {"schema_version": 2, "created_at": now(), "snapshot": provenance(repository, commit, run_id),
            "rounds": rounds, "desktop": {"testbeds": planned_testbeds(optional), "benchmarks": expected_benchmarks()},
            "mobile": {"platforms": ["ios", "android"], "functions": list(mobile_report.FUNCTIONS),
                       "warmup": 1, "iterations": 3}}
    return validate_plan(plan)


def validate_plan(plan):
    require(set(plan) == {"schema_version", "created_at", "snapshot", "rounds", "desktop", "mobile"}, "invalid plan fields")
    require(type(plan["schema_version"]) is int and plan["schema_version"] == 2, "unsupported plan schema")
    instant(plan["created_at"])
    validate_source(plan["snapshot"])
    integer(plan["rounds"], 100)
    testbeds = plan["desktop"].get("testbeds")
    require(isinstance(testbeds, list) and testbeds == planned_testbeds(testbeds[len(TESTBEDS):]), "incomplete desktop plan")
    require(plan["desktop"] == {"testbeds": testbeds, "benchmarks": expected_benchmarks()}, "incomplete desktop plan")
    require(plan["mobile"] == {"platforms": ["ios", "android"], "functions": list(mobile_report.FUNCTIONS),
                               "warmup": 1, "iterations": 3}, "incomplete mobile plan")
    return plan


def digest(document, length=64):
    return hashlib.sha256(json.dumps(document, sort_keys=True, separators=(",", ":")).encode()).hexdigest()[:length]


def machine_id(machine):
    return digest({key: machine[key] for key in ("name", "arch", "os", "cpu", "logical_cpus")}, 16)


def validate_machine(machine, desktop=False):
    require(set(machine) == {"id", "name", "arch", "os", "cpu", "logical_cpus", "memory_bytes"}, "invalid machine fields")
    for key in ("name", "arch", "os"):
        text(machine[key])
    if desktop or machine["cpu"] is not None:
        text(machine["cpu"])
    for key in ("logical_cpus", "memory_bytes"):
        if desktop or machine[key] is not None:
            integer(machine[key])
    require(machine["id"] == machine_id(machine), "machine identity mismatch")


def sysctl(name):
    return subprocess.check_output(["sysctl", "-n", name], text=True).strip()


def hardware(testbed):
    if testbed == "macos-arm64":
        require(platform.system() == "Darwin" and platform.machine() == "arm64", "testbed requires an Apple silicon Mac")
        cpu = text(sysctl("machdep.cpu.brand_string"))
        machine = {"name": cpu, "cpu": cpu, "arch": "arm64", "os": f"macOS {platform.mac_ver()[0]}",
                   "logical_cpus": int(sysctl("hw.logicalcpu")), "memory_bytes": int(sysctl("hw.memsize"))}
        machine["id"] = machine_id(machine)
        validate_machine(machine, desktop=True)
        return machine
    require(platform.system() == "Linux", "desktop measurement requires a Linux native runner")
    arch = {"x86_64": "x86-64", "aarch64": "arm64"}.get(platform.machine())
    require(arch == testbed, "runner architecture does not match testbed")
    fields = {}
    for line in Path("/proc/cpuinfo").read_text().splitlines():
        key, separator, value = line.partition(":")
        if separator:
            fields.setdefault(key.strip(), value.strip())
    cpu = fields.get("model name") or fields.get("Model") or fields.get("Hardware")
    if not cpu and "CPU implementer" in fields and "CPU part" in fields:
        cpu = f"ARM implementer {fields['CPU implementer']}, part {fields['CPU part']}, revision {fields.get('CPU revision', 'unknown')}"
    text(cpu)
    machine = {"name": cpu, "cpu": cpu, "arch": arch, "os": f"Linux {platform.release()}",
               "logical_cpus": os.cpu_count(),
               "memory_bytes": os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")}
    machine["id"] = machine_id(machine)
    validate_machine(machine, desktop=True)
    return machine


def validate_metrics(results, benchmark):
    require(set(results) == set(expected_results(benchmark)), "unexpected workload or incomplete aggregation")
    explicit = workload(expected_results(benchmark)[0])[4]
    require(explicit is not None, "desktop timing requires an explicit thread count")
    for metrics in results.values():
        latency = metrics["latency"]
        positive(latency["value"])
        require(latency["value"] == latency["lower_value"] == latency["upper_value"], "round is not one timing sample")
        verify = metrics["verify"]
        require(positive(verify["lower_value"]) <= positive(verify["value"]) <= positive(verify["upper_value"]), "invalid verification timing")
        positive(metrics["proof-size"]["value"])
        threads, efficiency = pool_threads(metrics)
        require(threads - efficiency == explicit, "measured thread count mismatch")
        if explicit == 16:
            require(efficiency == 0, "fixed16 pool topology mismatch")
        integer(metrics["peak-memory"]["value"], mobile_report.MAX_SAFE_INTEGER)


def pool_threads(metrics):
    """The pool's total and efficiency workers. `LEANVM_NUM_THREADS` names the performance
    workers, so a named 1/4/8 case on a host with efficiency cores runs those on top."""
    threads = integer(metrics["threads"]["value"], 1024)
    performance = integer(metrics["performance-threads"]["value"], 1024)
    efficiency = metrics["efficiency-threads"]["value"]
    require(type(efficiency) is int and efficiency >= 0 and performance + efficiency == threads, "inconsistent pool topology")
    return threads, efficiency


def run_desktop(plan, testbed, benchmark, executable):
    validate_plan(plan)
    require(testbed in plan["desktop"]["testbeds"] and benchmark in plan["desktop"]["benchmarks"], "unplanned desktop case")
    source = plan["snapshot"]
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    require(head == source["commit"], "checkout revision does not match plan")
    if os.environ.get("GITHUB_ACTIONS") == "true" or os.environ.get("CI"):
        require(os.environ.get("GITHUB_REPOSITORY") == source["repository"], "CI repository does not match plan")
        require(os.environ.get("GITHUB_RUN_ID") == str(source["run_id"]), "CI run does not match plan")
    machine = hardware(testbed)
    count = workload(expected_results(benchmark)[0])[4]
    integer(count, 1024)
    environment = dict(os.environ, LEANVM_NUM_THREADS=str(count))
    document = {"schema_version": 2, "snapshot": source, "plan_id": digest(plan), "testbed": testbed,
                "benchmark": benchmark, "machine": machine, "threads": count, "samples": []}
    for number in range(1, plan["rounds"] + 1):
        completed = subprocess.run([str(Path(executable).resolve()), "bench", "--only", benchmark,
                                    "--repeat", "1", "--cooldown", "0"],
                                   cwd=ROOT, env=environment, stdout=subprocess.PIPE, text=True, check=True)
        results = decode(completed.stdout)
        validate_metrics(results, benchmark)
        document["samples"].append({"round": number, "measured_at": now(), "exit_code": completed.returncode,
                                    "threads": count, "results": results})
    desktop_rows(document, plan, testbed, benchmark)
    return document


def row(title, description, path, category, count, samples, machine, source, measured_at, verification,
        peak_memory_bytes, peak_memory_method, thread_label=None):
    identity = [title, description, category, machine["id"], count, thread_label]
    return {"id": digest(identity, 24), "program": {"name": title,
            "source_url": f"https://github.com/{source['repository']}/blob/{source['commit']}/{path}"},
            "workload": description, "category": category, "machine": machine,
            "threads": {"count": count, "label": thread_label or f"{count} thread{'s' if count != 1 else ''}"},
            "median_seconds": statistics.median(samples), "min_seconds": min(samples), "max_seconds": max(samples),
            "peak_memory_bytes": peak_memory_bytes, "peak_memory_method": peak_memory_method,
            "samples_seconds": samples, "measured_at": measured_at, "verification": verification}


def desktop_rows(document, plan, testbed, benchmark):
    require(type(document["schema_version"]) is int and document["schema_version"] == 2, "unsupported desktop schema")
    validate_source(document["snapshot"])
    require(document["snapshot"] == plan["snapshot"] and document["plan_id"] == digest(plan), "desktop source or plan mismatch")
    require(document["testbed"] == testbed and document["benchmark"] == benchmark, "desktop case mismatch")
    machine = document["machine"]
    validate_machine(machine, desktop=True)
    require(machine["arch"] == TESTBED_ARCH[testbed], "desktop architecture mismatch")
    count = integer(document["threads"], 1024)
    explicit = workload(expected_results(benchmark)[0])[4]
    require(explicit == count, "named thread count mismatch")
    samples = document["samples"]
    require(len(samples) == plan["rounds"], "incomplete desktop rounds")
    require(all(type(sample["round"]) is int for sample in samples), "invalid round")
    require({sample["round"] for sample in samples} == set(range(1, plan["rounds"] + 1)), "duplicate or missing rounds")
    samples = sorted(samples, key=lambda sample: sample["round"])
    previous = instant(plan["created_at"])
    for sample in samples:
        measured = instant(sample["measured_at"])
        require(previous <= measured <= datetime.now(timezone.utc), "stale or unordered desktop sample")
        previous = measured
        require(type(sample["exit_code"]) is int and sample["exit_code"] == 0, "failed desktop proof")
        require(type(sample["threads"]) is int and sample["threads"] == count, "inconsistent desktop threads")
        validate_metrics(sample["results"], benchmark)
    rows = []
    for name in expected_results(benchmark):
        title, description, path, category, _ = workload(name)
        pools = {pool_threads(sample["results"][name]) for sample in samples}
        require(len(pools) == 1, "inconsistent pool across rounds")
        threads, efficiency = pools.pop()
        label = None
        if efficiency:
            label = f"{threads} threads ({threads - efficiency} performance + {efficiency} efficiency)"
        timings = [sample["results"][name]["latency"]["value"] / 1e9 for sample in samples]
        peak_memory = max(sample["results"][name]["peak-memory"]["value"] for sample in samples)
        units = ("bytes on macOS" if machine["os"].startswith("macOS ") else "KiB converted to bytes")
        memory_method = (
            f"Maximum {machine['os'].split()[0]} process RSS high-water mark across independent rounds, from CLI BMF "
            f"peak-memory.value in bytes (getrusage(RUSAGE_SELF).ru_maxrss, {units}). Includes process setup and prior work."
        )
        if category == "aggregation":
            memory_method += " Aggregation includes leaf preparation; higher-node peaks can include preceding first-level work."
        verification = {"verified_proofs": len(samples), "total_proofs": len(samples),
                        "method": "Successful leanvm bench process and proof verification timing for every independent round",
                        "verify_seconds": [sample["results"][name]["verify"]["value"] / 1e9 for sample in samples]}
        rows.append(row(title, description, path, category, threads, timings, machine, plan["snapshot"],
                        samples[-1]["measured_at"], verification, peak_memory, memory_method, label))
    return rows


def mobile_rows(directory, plan, platform_name):
    metadata = load(directory / "metadata.json")
    raw = load(directory / "raw-results.json")
    source = plan["snapshot"]
    # Share the mobile reporter's full device, function, metrics and sample validation.
    _, complete, observed_platform = mobile_report.render(directory, source["repository"], source["commit"], str(source["run_id"]))
    require(complete and observed_platform == platform_name, "missing or wrong mobile platform")
    measured = mobile_report.validate_results(raw, platform_name)
    timestamp = metadata["measured_at"]
    require(instant(plan["created_at"]) <= instant(timestamp) <= datetime.now(timezone.utc), "stale mobile sample")
    require(metadata["timestamp_basis"] == "collection_completed_at", "unexpected mobile timestamp basis")
    model, version, os_name = mobile_report.DEVICES[platform_name]
    machine = {"name": model, "arch": "aarch64", "os": f"{os_name} {version}", "cpu": metadata.get("soc"),
               "logical_cpus": None, "memory_bytes": None}
    machine["id"] = machine_id(machine)
    definitions = {
        mobile_report.FUNCTION: ("Shielded transfers", "2 spends, 4 input notes; standalone proof, leaf log inverse rate 2",
                                 "programs/shielded/guest/src/main.rs", "program"),
        mobile_report.AGGREGATE_FUNCTION: ("Shielded aggregation",
            "2 to 1; two independently proven 2-spend leaves, 4 spends and 8 input notes total; leaf setup excluded; leaf rate 1/4, tree rate 1/2",
            "bench-mobile/src/lib.rs", "aggregation"),
        mobile_report.FALCON_FUNCTION: ("Falcon-512", "Verify 1 signature",
                                       "programs/falcon/guest/src/main.rs", "program"),
        mobile_report.STATEPROOF_FUNCTION: ("L1 state proofs", "Verify 1 account and 1 storage slot",
                                           "programs/stateproof/guest/src/main.rs", "program"),
    }
    rows = []
    for function in mobile_report.FUNCTIONS:
        result = measured[function]
        metrics = metadata["benchmarks"][function]
        verification = {"verified_proofs": metrics["verified_proofs"], "total_proofs": metadata["warmup"] + metadata["iterations"],
                        "parameters": metrics}
        result_row = row(*definitions[function], metrics["threads"], [value / 1e9 for value in result["samples_ns"]],
                         machine, source, timestamp, verification, mobile_report.peak_memory_bytes(result),
                         mobile_report.peak_memory_method(platform_name))
        result_row["timestamp_basis"] = metadata["timestamp_basis"]
        rows.append(result_row)
    return rows


def validate(snapshot):
    require(set(snapshot) == {"schema_version", "generated_at", "snapshot", "results"}, "invalid snapshot fields")
    require(type(snapshot["schema_version"]) is int and snapshot["schema_version"] == 3, "unsupported schema")
    results = snapshot["results"]
    require(isinstance(results, list) and len(results) <= 10000, "invalid results")
    if snapshot["snapshot"] is None:
        require(snapshot["generated_at"] is None and results == [], "invalid unpublished snapshot")
        return snapshot
    validate_source(snapshot["snapshot"])
    generated = instant(snapshot["generated_at"])
    require(results, "published snapshot cannot be empty")
    source = snapshot["snapshot"]
    prefix = f"https://github.com/{source['repository']}/blob/{source['commit']}/"
    seen, identities = set(), set()
    required = {"id", "program", "workload", "category", "machine", "threads", "median_seconds", "min_seconds",
                "max_seconds", "samples_seconds", "measured_at", "verification", "peak_memory_bytes", "peak_memory_method"}
    for result in results:
        require(required <= result.keys() and result.keys() <= required | {"timestamp_basis"}, "invalid result fields")
        require(isinstance(result["id"], str) and re.fullmatch(r"[0-9a-f]{24}", result["id"]), "invalid result id")
        require(result["id"] not in seen, "duplicate result")
        seen.add(result["id"])
        require(result["category"] in ("program", "aggregation"), "unsupported category")
        require(set(result["program"]) == {"name", "source_url"}, "invalid program fields")
        text(result["program"]["name"])
        url = result["program"]["source_url"]
        require(isinstance(url, str) and url.startswith(prefix) and len(url) > len(prefix)
                and not any(part in (".", "..") for part in url[len(prefix):].split("/")), "source link does not pin snapshot")
        text(result["workload"])
        validate_machine(result["machine"])
        require(set(result["threads"]) == {"count", "label"}, "invalid thread fields")
        integer(result["threads"]["count"], 1024)
        text(result["threads"]["label"])
        identity = (result["program"]["name"], result["workload"], result["category"], result["machine"]["id"],
                    result["threads"]["count"], result["threads"]["label"])
        require(identity not in identities, "duplicate configuration")
        identities.add(identity)
        require(instant(result["measured_at"]) <= generated, "measurement after publication")
        if "timestamp_basis" in result:
            text(result["timestamp_basis"])
        samples = result["samples_seconds"]
        require(isinstance(samples, list) and 0 < len(samples) <= 100, "invalid samples")
        for sample in samples:
            positive(sample)
        for field in ("median_seconds", "min_seconds", "max_seconds"):
            positive(result[field])
        integer(result["peak_memory_bytes"], mobile_report.MAX_SAFE_INTEGER)
        require(text(result["peak_memory_method"]).strip(), "empty peak memory method")
        require(result["median_seconds"] == statistics.median(samples), "median mismatch")
        require(result["min_seconds"] == min(samples) and result["max_seconds"] == max(samples), "range mismatch")
        verification = result["verification"]
        verified = integer(verification["verified_proofs"])
        require(verified == integer(verification["total_proofs"]) and verified >= len(samples), "unverified samples")
        if "verify_seconds" in verification:
            require(len(verification["verify_seconds"]) == len(samples), "missing verification evidence")
            for value in verification["verify_seconds"]:
                positive(value)
        if "parameters" in verification:
            parameters = verification["parameters"]
            require(parameters["threads"] == parameters["available_parallelism"] == result["threads"]["count"], "inconsistent mobile threads")
            require(parameters["verified_proofs"] == verified, "inconsistent verification evidence")
    return snapshot


def publish(plan, artifacts, output):
    validate_plan(plan)
    artifacts = Path(artifacts)
    expected = {f"snapshot-result-desktop-{testbed}-{benchmark}": (testbed, benchmark)
                for testbed in plan["desktop"]["testbeds"] for benchmark in plan["desktop"]["benchmarks"]}
    mobile = {f"snapshot-result-mobile-{name}": name for name in plan["mobile"]["platforms"]}
    require({entry.name for entry in artifacts.iterdir()} == expected.keys() | mobile.keys(), "missing, duplicate or unexpected result artifacts")
    rows = []
    machines = {}
    for name, (testbed, benchmark) in expected.items():
        directory = artifacts / name
        require(directory.is_dir() and not directory.is_symlink(), "unsafe desktop artifact")
        require({entry.name for entry in directory.iterdir()} == {"result.json"}, "unexpected desktop artifact files")
        document = load(directory / "result.json")
        rows.extend(desktop_rows(document, plan, testbed, benchmark))
        identity = document["machine"]["id"]
        require(machines.setdefault(testbed, identity) == identity, "inconsistent testbed hardware")
    for name, platform_name in mobile.items():
        directory = artifacts / name
        require(directory.is_dir() and not directory.is_symlink(), "unsafe mobile artifact")
        require({entry.name for entry in directory.iterdir()} == {"metadata.json", "raw-results.json"}, "unexpected mobile artifact files")
        rows.extend(mobile_rows(directory, plan, platform_name))
    snapshot = validate({"schema_version": 3, "generated_at": now(), "snapshot": plan["snapshot"],
                         "results": sorted(rows, key=lambda result: result["id"])})
    atomic_write(output, snapshot)
    return snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    plan = commands.add_parser("plan", help="Create an immutable complete fresh-run plan")
    plan.add_argument("--repository", required=True)
    plan.add_argument("--commit", required=True)
    plan.add_argument("--run-id", required=True, type=int)
    plan.add_argument("--rounds", type=int, default=5)
    plan.add_argument("--optional-testbed", action="append", default=[], choices=OPTIONAL_TESTBEDS)
    plan.add_argument("--output", type=Path, required=True)
    desktop = commands.add_parser("run-desktop", help="Measure one planned case on its native runner")
    desktop.add_argument("--plan", type=Path, required=True)
    desktop.add_argument("--testbed", choices=TESTBEDS + OPTIONAL_TESTBEDS, required=True)
    desktop.add_argument("--benchmark", required=True)
    desktop.add_argument("--executable", type=Path, required=True)
    desktop.add_argument("--output", type=Path, required=True)
    publication = commands.add_parser("publish", help="Validate all fresh artifacts and atomically replace the snapshot")
    publication.add_argument("--plan", type=Path, required=True)
    publication.add_argument("--artifacts", type=Path, required=True)
    publication.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("check", help="Validate a schema-3 snapshot or the honest unpublished bootstrap")
    check.add_argument("--input", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "plan":
            document = make_plan(args.repository, args.commit, args.run_id, args.rounds, args.optional_testbed)
            atomic_write(args.output, document, immutable=True)
            print(json.dumps(document["desktop"]["benchmarks"]))
        elif args.command == "run-desktop":
            document = run_desktop(load(args.plan), args.testbed, args.benchmark, args.executable)
            atomic_write(args.output, document)
        elif args.command == "publish":
            snapshot = publish(load(args.plan), args.artifacts, args.output)
            print(f"Published {len(snapshot['results'])} rows to {args.output}")
        else:
            snapshot = validate(load(args.input))
            print(f"Valid schema-3 snapshot: {len(snapshot['results'])} rows")
    except (ValueError, KeyError, TypeError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, f"benchmark-site: {error}\n")


if __name__ == "__main__":
    main()
