"""Regression checks for the main Lean formalization path filter."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest
from unittest.mock import Mock, patch


selector = runpy.run_path(str(Path(__file__).with_name("lean-vm-changes.py")))["needs_formalization"]
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

    def records(self, endpoint, collection):
        if collection == "workflow_runs":
            self.assertEqual(
                endpoint,
                f"repos/{repository}/actions/workflows/lean.yml/runs?branch=main&status=completed&per_page=100",
            )
            return self.runs
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
        self.assertTrue(selector())
        with patch.dict(selector.__globals__, records=Mock(side_effect=OSError("unavailable"))):
            self.assertTrue(selector())
        with patch.dict(selector.__globals__, checked_main_base=lambda: "not-a-commit"):
            self.assertTrue(selector())

    def test_dispatch_runs_and_pull_request_uses_its_base(self):
        os.environ["GITHUB_EVENT_NAME"] = "workflow_dispatch"
        self.assertTrue(selector())
        os.environ["GITHUB_EVENT_NAME"] = "pull_request"
        self.git("remote", "add", "origin", str(Path.cwd()))
        self.assertFalse(selector())
        os.environ["BASE"] = self.old
        self.assertTrue(selector())


if __name__ == "__main__":
    unittest.main()
