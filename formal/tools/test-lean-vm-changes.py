"""Regression checks for the main Lean formalization path filter."""

from contextlib import redirect_stdout
from io import StringIO
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch


module = runpy.run_path(str(Path(__file__).with_name("lean-vm-changes.py")))
selector = module["needs_formalization"]
repository = "leanEthereum/leanVM"


class FormalizationChanges(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        previous = Path.cwd()
        self.addCleanup(os.chdir, previous)
        os.chdir(directory.name)
        self.git("init", "--quiet")
        self.git("config", "user.email", "test@example.com")
        self.git("config", "user.name", "Test")
        self.old = self.commit("crates/verifier", "old")
        self.changed = self.commit("crates/verifier", "changed")
        self.release = self.commit("bindings/release", "release")
        self.runs = []
        self.jobs = {}
        self.queried_heads = []
        self.addCleanup(patch.stopall)
        patch.dict(
            os.environ,
            GITHUB_EVENT_NAME="push",
            GITHUB_REPOSITORY=repository,
            GITHUB_RUN_NUMBER="100",
            BASE=self.changed,
        ).start()
        patch.dict(selector.__globals__, records=self.records).start()

    def git(self, *args):
        return subprocess.check_output(["git", *args], text=True).strip()

    def commit(self, name, contents):
        path = Path(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")
        self.git("add", name)
        self.git("commit", "--quiet", "-m", name)
        return self.git("rev-parse", "HEAD")

    def records(self, endpoint, collection, deadline):
        if collection == "workflow_runs":
            prefix, commit = endpoint.split("&head_sha=")
            self.assertEqual(
                prefix,
                f"repos/{repository}/actions/workflows/lean.yml/runs?branch=main&status=completed",
            )
            commit, page_size = commit.split("&")
            self.assertEqual(page_size, "per_page=100")
            self.queried_heads.append(commit)
            return [run for run in self.runs if run["head_sha"] == commit]
        prefix, run, _, attempt, _ = endpoint.rsplit("/", 4)
        self.assertEqual(prefix, f"repos/{repository}/actions/runs")
        self.assertEqual(collection, "jobs")
        return self.jobs[int(run), int(attempt)]

    def record(self, commit, job_result, **run_fields):
        run_id = len(self.runs) + 1
        self.runs.append({
            "repository": {"full_name": repository},
            "head_repository": {"full_name": repository},
            "head_branch": "main",
            "head_sha": commit,
            "path": ".github/workflows/lean.yml",
            "event": "push",
            "status": "completed",
            "conclusion": "success",
            "id": run_id,
            "run_number": run_id,
            "run_attempt": 2,
            **run_fields,
        })
        jobs = [{
            "name": "lean-vm-formalization",
            "status": "completed",
            "conclusion": job_result,
            "head_sha": commit,
            "id": run_id + 100,
            "run_id": run_id,
            "run_attempt": 2,
        }] if job_result else []
        self.jobs[run_id, 2] = jobs
        return jobs

    def test_cancelled_change_and_green_skip_do_not_advance_base(self):
        self.record(self.changed, None, conclusion="cancelled")
        self.record(self.release, "skipped")
        self.record(self.old, "success")
        self.assertTrue(selector())

    def test_first_parent_order_selects_closest_success(self):
        self.record(self.old, "success")
        self.record(self.changed, "success")
        self.assertFalse(selector())
        self.assertEqual(self.queried_heads, [self.release, self.changed])

    def test_future_fork_and_unrelated_jobs_do_not_advance_base(self):
        self.record(self.changed, "success", event="pull_request")
        self.record(self.changed, "success", head_repository={"full_name": "fork/leanVM"})
        self.record(self.changed, "success", run_number=101)
        self.record(self.changed, "success", path=".github/workflows/other.yml")
        self.record(self.changed, "failure")
        self.record(self.changed, "success")[0]["run_attempt"] = 1
        self.record(self.changed, "success")[0]["name"] = "lean-vm-changes"
        self.record(self.old, "success")
        self.assertTrue(selector())

    def test_history_rewrite_disqualifies_checked_commit(self):
        self.record(self.release, "success")
        self.record(self.old, "success")
        self.git("checkout", "--quiet", "--detach", self.old)
        self.commit("bindings/release", "rewritten")
        self.commit("crates/verifier", "changed")
        os.environ["BASE"] = self.release
        self.assertTrue(selector())

    def test_gate_change_requires_new_check(self):
        self.record(self.release, "success")
        self.commit(".github/workflows/lean.yml", "new check")
        self.assertTrue(selector())

    def test_lookup_and_comparison_errors_require_full_check(self):
        self.assert_warning("No successful formalization job found")
        error = OSError("unavailable\n::error::unexpected subprocess output")
        with patch.dict(selector.__globals__, records=Mock(side_effect=error)):
            self.assert_warning("Could not confirm the formalization baseline")
        with patch.dict(selector.__globals__, checked_main_base=lambda: "not-a-commit"):
            self.assert_warning("Could not compare the formalization baseline")

    def assert_warning(self, reason):
        output = StringIO()
        with redirect_stdout(output):
            self.assertTrue(selector())
        lines = output.getvalue().splitlines()
        self.assertEqual(len(lines), 1)
        self.assertTrue(lines[0].startswith(f"::warning::{reason}"))

    def test_lookup_uses_one_page_and_stops_at_the_deadline(self):
        read_records = module["records"]
        with patch("time.monotonic", side_effect=[10, 15]), patch(
            "subprocess.check_output", return_value='{"name":"job"}\n'
        ) as api:
            self.assertEqual(read_records("endpoint", "jobs", 15), [{"name": "job"}])
            with self.assertRaises(TimeoutError):
                read_records("endpoint", "jobs", 15)
        api.assert_called_once_with(
            ["gh", "api", "--jq", ".jobs[] | @json", "endpoint"],
            stderr=subprocess.PIPE,
            text=True,
            timeout=5,
        )

    def test_dispatch_runs_and_pull_request_uses_its_base(self):
        os.environ["GITHUB_EVENT_NAME"] = "workflow_dispatch"
        self.assertTrue(selector())
        os.environ["GITHUB_EVENT_NAME"] = "pull_request"
        self.git("remote", "add", "origin", str(Path.cwd()))
        self.assertFalse(selector())
        os.environ["BASE"] = self.old
        self.assertTrue(selector())

    def test_pull_request_fetch_failure_warns_without_git_output(self):
        script = Path(__file__).with_name("lean-vm-changes.py")
        output = Path.cwd() / "changed"
        run = subprocess.run(
            [sys.executable, "-I", str(script)],
            env={**os.environ, "GITHUB_EVENT_NAME": "pull_request", "GITHUB_OUTPUT": str(output)},
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertEqual(run.stderr, "")
        self.assertEqual(
            run.stdout,
            "::warning::Could not confirm the formalization baseline. Running the full Lean formalization check.\n",
        )
        self.assertEqual(output.read_text(encoding="utf-8"), "changed=true\n")


if __name__ == "__main__":
    unittest.main()
