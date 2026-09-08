"""Runner contract: execute every check, retain failures, and bind actual inputs."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts.verify import source_snapshot, verify


COMMANDS = [
    ["lake", "build"],
    ["lake", "build", "Corpus.Audit"],
    ["lake", "env", "lean", "Corpus/Audit.lean"],
    ["lake", "env", "lean", "Corpus/AuditChecks.lean"],
]
SNAPSHOT = {"commit": "a" * 40, "toolchain": "leanprover/lean4:v4.28.0",
            "sourceFilesSha256": {"Corpus.lean": "b" * 64}}


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.out = self.root / "out"
        self.calls = []

    def good(self, argv, cwd):
        self.calls.append(argv)
        self.assertEqual(cwd, self.root)
        if argv[-1] == "Corpus/Audit.lean":
            return 0, "audit green: checked\n"
        if argv[-1] == "Corpus/AuditChecks.lean":
            return 0, "public admission checks: checked\npublic coverage checks: checked\npublic supporting coverage checks: checked\n"
        return 0, "build completed\n"

    def check(self, run=None, snapshot=None):
        return verify(self.root, self.out, run=run or self.good,
                      snapshot=snapshot or (lambda root: dict(SNAPSHOT)))

    def test_success_runs_all_phases_and_records_inputs(self):
        result = self.check()
        self.assertEqual(self.calls, COMMANDS)
        self.assertTrue(result["complete"])
        self.assertEqual(result["inputs"], SNAPSHOT)
        self.assertEqual(len(result["phases"]), 4)
        self.assertEqual(json.loads((self.out / "verification.json").read_text()), result)
        self.assertTrue(all((self.out / p["log"]).is_file() for p in result["phases"]))

    def test_failed_phase_stops_and_retains_its_output(self):
        def fail(argv, cwd):
            self.good(argv, cwd)
            return 9, "kernel failure\n"
        result = self.check(run=fail)
        self.assertFalse(result["complete"])
        self.assertEqual(self.calls, COMMANDS[:1])
        self.assertEqual(result["phases"][0]["exitCode"], 9)
        self.assertIn("kernel failure", (self.out / result["phases"][0]["log"]).read_text())

    def test_zero_exit_without_audit_result_is_failure(self):
        def missing(argv, cwd):
            code, text = self.good(argv, cwd)
            return code, "" if argv[-1] == "Corpus/Audit.lean" else text
        result = self.check(run=missing)
        self.assertFalse(result["complete"])
        self.assertEqual(self.calls, COMMANDS[:3])
        self.assertIn("audit green:", result["phases"][-1]["missingMarkers"])

    def test_coverage_tests_cannot_silently_disappear(self):
        def missing(argv, cwd):
            code, text = self.good(argv, cwd)
            return code, text.replace("public coverage checks:", "removed checks:")
        result = self.check(run=missing)
        self.assertFalse(result["complete"])
        self.assertIn("public coverage checks:", result["phases"][-1]["missingMarkers"])

    def test_supporting_coverage_test_cannot_silently_disappear(self):
        def missing(argv, cwd):
            code, text = self.good(argv, cwd)
            return code, text.replace("public supporting coverage checks:", "removed checks:")
        result = self.check(run=missing)
        self.assertFalse(result["complete"])
        self.assertIn("public supporting coverage checks:", result["phases"][-1]["missingMarkers"])

    def test_source_snapshot_binds_edits_and_runner_but_excludes_outputs(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")
        (self.root / "Corpus.lean").write_text("import Init\n")
        (self.root / "scripts").mkdir()
        (self.root / "scripts/verify.py").write_text("runner source\n")
        self.out.mkdir()
        (self.out / "report.json").write_text("generated output")
        first = source_snapshot(self.root)
        self.assertEqual(set(first["sourceFilesSha256"]),
                         {"lean-toolchain", "Corpus.lean", "scripts/verify.py"})
        self.assertIsNone(first["checkoutCommit"])
        (self.root / "Corpus.lean").write_text("import Init.Prelude\n")
        self.assertNotEqual(first, source_snapshot(self.root))

    def test_source_symlink_is_unavailable_instead_of_unbound(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")
        (self.root / "linked.lean").symlink_to(self.root / "lean-toolchain")
        with self.assertRaisesRegex(ValueError, "source symlinks"):
            source_snapshot(self.root)

    def test_input_change_invalidates_otherwise_successful_run(self):
        snapshots = iter([SNAPSHOT, {**SNAPSHOT, "commit": "c" * 40}])
        result = self.check(snapshot=lambda root: next(snapshots))
        self.assertFalse(result["complete"])
        self.assertIn("inputs changed during verification", result["errors"])

    def test_old_success_is_replaced_before_any_command_runs(self):
        self.out.mkdir()
        (self.out / "verification.json").write_text('{"complete": true}')
        def fail(argv, cwd):
            self.assertFalse(json.loads((self.out / "verification.json").read_text())["complete"])
            return 1, "failure\n"
        result = self.check(run=fail)
        self.assertFalse(result["complete"])

    def test_command_launch_exception_is_recorded_as_failure(self):
        def fail(argv, cwd):
            raise OSError("executable unavailable")
        result = self.check(run=fail)
        self.assertFalse(result["complete"])
        self.assertIn("executable unavailable", result["errors"][0])

    def test_snapshot_failure_cannot_retain_old_success(self):
        self.out.mkdir()
        (self.out / "verification.json").write_text('{"complete": true}')
        def fail(root):
            raise ValueError("unbound source")
        result = self.check(snapshot=fail)
        self.assertFalse(result["complete"])
        self.assertEqual(self.calls, [])
        self.assertFalse(json.loads((self.out / "verification.json").read_text())["complete"])


if __name__ == "__main__":
    unittest.main()
