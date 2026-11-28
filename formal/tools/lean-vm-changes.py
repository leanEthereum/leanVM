"""Select when CI needs to run lean-vm-formalization."""

import json
import os
from pathlib import Path
import subprocess
import time


WORKFLOW = ".github/workflows/lean.yml"
WATCHED = ("formal", "crates", "guests", "Cargo.toml", "Cargo.lock", ".cargo/config.toml", WORKFLOW)
HISTORY_DEPTH = 64
LOOKUP_SECONDS = 45


def records(endpoint, collection, deadline):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError("formalization baseline lookup timed out")
    output = subprocess.check_output(
        ["gh", "api", "--jq", f".{collection}[] | @json", endpoint],
        stderr=subprocess.PIPE,
        text=True,
        timeout=remaining,
    )
    return [json.loads(line) for line in output.splitlines()]


def checked_main_base():
    repository = os.environ["GITHUB_REPOSITORY"]
    run_number = int(os.environ["GITHUB_RUN_NUMBER"])
    ancestors = subprocess.check_output(
        ["git", "rev-list", "--first-parent", f"--max-count={HISTORY_DEPTH}", "HEAD"],
        stderr=subprocess.PIPE,
        text=True,
    ).splitlines()
    deadline = time.monotonic() + LOOKUP_SECONDS
    # Read one page for each first-parent commit. Traverse commits in order because
    # workflow runs and reruns can finish in any order.
    for commit in ancestors:
        runs = records(
            f"repos/{repository}/actions/workflows/lean.yml/runs"
            f"?branch=main&status=completed&head_sha={commit}&per_page=100",
            "workflow_runs",
            deadline,
        )
        for run in runs:
            if not (
                run["event"] in ("push", "workflow_dispatch")
                and run["head_sha"] == commit
                and run["repository"]["full_name"].casefold() == repository.casefold()
                and run["head_repository"]["full_name"].casefold() == repository.casefold()
                and run["head_branch"] == "main"
                and run["path"].partition("@")[0] == WORKFLOW
                and run["status"] == "completed"
                and 0 < run["run_number"] < run_number
            ):
                continue
            run_id = int(run["id"])
            attempt = int(run["run_attempt"])
            jobs = records(
                f"repos/{repository}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100",
                "jobs",
                deadline,
            )
            for job in jobs:
                if (
                    job["name"] == "lean-vm-formalization"
                    and job["status"] == "completed"
                    and job["conclusion"] == "success"
                    and job["head_sha"] == commit
                    and job["run_id"] == run_id
                    and job["run_attempt"] == attempt
                ):
                    print(f"Checked base {commit} from run {run_id}, attempt {attempt}, job {int(job['id'])}.")
                    return commit
    return None


def run_full_check(reason):
    print(f"::warning::{reason} Running the full Lean formalization check.")
    return True


def needs_formalization():
    try:
        event = os.environ["GITHUB_EVENT_NAME"]
        if event == "workflow_dispatch":
            return True
        if event == "push":
            base = checked_main_base()
        else:
            base = os.environ["BASE"]
            subprocess.run(
                ["git", "fetch", "--quiet", "--depth=1", "origin", base],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                check=True,
            )
        if base is None:
            return run_full_check("No successful formalization job found for the fetched main history.")
        comparison = subprocess.run(
            ["git", "diff", "--quiet", base, "HEAD", "--", *WATCHED],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )
        if comparison.returncode not in (0, 1):
            return run_full_check("Could not compare the formalization baseline with HEAD.")
        return comparison.returncode == 1
    except (AttributeError, KeyError, TypeError, ValueError, OSError, subprocess.SubprocessError):
        return run_full_check("Could not confirm the formalization baseline.")


if __name__ == "__main__":
    result = "true" if needs_formalization() else "false"
    with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as output:
        output.write(f"changed={result}\n")
