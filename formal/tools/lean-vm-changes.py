"""Select when CI needs to run lean-vm-formalization."""

import json
import os
from pathlib import Path
import subprocess
import sys


WORKFLOW = ".github/workflows/lean.yml"
WATCHED = ("formal", "crates", "guests", "Cargo.toml", "Cargo.lock", ".cargo/config.toml", WORKFLOW)


def records(endpoint, collection):
    output = subprocess.check_output(
        ["gh", "api", "--paginate", "--jq", f".{collection}[] | @json", endpoint],
        text=True,
        timeout=45,
    )
    return [json.loads(line) for line in output.splitlines()]


def checked_main_base():
    repository = os.environ["GITHUB_REPOSITORY"]
    run_number = int(os.environ["GITHUB_RUN_NUMBER"])
    ancestors = subprocess.check_output(
        ["git", "rev-list", "--first-parent", "HEAD"], text=True
    ).splitlines()
    runs = records(
        f"repos/{repository}/actions/workflows/lean.yml/runs?branch=main&status=completed&per_page=100",
        "workflow_runs",
    )
    ancestor_commits = set(ancestors)
    by_commit = {}
    for run in runs:
        if (
            run["event"] in ("push", "workflow_dispatch")
            and run["head_sha"] in ancestor_commits
            and run["repository"]["full_name"].casefold() == repository.casefold()
            and run["head_repository"]["full_name"].casefold() == repository.casefold()
            and run["head_branch"] == "main"
            and run["path"].partition("@")[0] == WORKFLOW
            and run["status"] == "completed"
            and 0 < run["run_number"] < run_number
        ):
            by_commit.setdefault(run["head_sha"], []).append(run)

    # The checkout can prove ancestry only within its fetched history. Traverse that
    # history in commit order, since a run and its reruns can finish in any order.
    for commit in ancestors:
        for run in by_commit.get(commit, ()):
            run_id = int(run["id"])
            attempt = int(run["run_attempt"])
            jobs = records(
                f"repos/{repository}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100",
                "jobs",
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
                    print(f"Checked base {commit} from run {run_id}, attempt {attempt}, job {job['id']}.")
                    return commit
    print("No successful formalization job found for the fetched main history.")
    return None


def needs_formalization():
    try:
        event = os.environ["GITHUB_EVENT_NAME"]
        if event == "workflow_dispatch":
            return True
        if event == "push":
            base = checked_main_base()
        else:
            base = os.environ["BASE"]
            subprocess.run(["git", "fetch", "--quiet", "--depth=1", "origin", base], check=True)
        if base is None:
            return True
        comparison = subprocess.run(["git", "diff", "--quiet", base, "HEAD", "--", *WATCHED])
        return comparison.returncode != 0
    except (AttributeError, KeyError, TypeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"Could not confirm the formalization baseline: {error}", file=sys.stderr)
        return True


if __name__ == "__main__":
    result = "true" if needs_formalization() else "false"
    with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as output:
        output.write(f"changed={result}\n")
