"""Run the public corpus checks and retain evidence, including failed phases.

This records repository CI. It is not the trusted operator admission service.
Run with Python 3.10+; there are no external Python dependencies.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Callable

PHASES = (
    ("build", ["lake", "build"], ()),
    ("audit-build", ["lake", "build", "Corpus.Audit"], ()),
    ("audit", ["lake", "env", "lean", "Corpus/Audit.lean"], ("audit green:",)),
    ("adversarial", ["lake", "env", "lean", "Corpus/AuditChecks.lean"],
     ("public admission checks:", "public coverage checks:",
      "public supporting coverage checks:")),
)
EXCLUDED = {".git", ".lake", "out", "__pycache__"}


def source_snapshot(root: Path) -> dict:
    """Bind actual source files, including uncommitted work and the runner itself."""
    files = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in EXCLUDED for part in relative.parts):
            continue
        if path.is_symlink():
            raise ValueError(f"source symlinks require a separate input contract: {relative}")
        if path.is_file():
            files[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    commit = None
    if (root / ".git").exists():
        commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
        ).strip()
    return {"checkoutCommit": commit,
            "toolchain": (root / "lean-toolchain").read_text().strip(),
            "sourceFilesSha256": files}


def run_command(argv: list[str], cwd: Path) -> tuple[int, str]:
    completed = subprocess.run(argv, cwd=cwd, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, check=False)
    return completed.returncode, completed.stdout


def verify(root: Path, out: Path, *, run: Callable = run_command,
           snapshot: Callable = source_snapshot) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    report = {"schemaVersion": 1, "scope": "public-corpus-verification-run",
              "authority": "repository-ci; trusted operator admission remains separate",
              "witnessKind": "lean-propositional-proof", "relation": "same-statement",
              "complete": False, "phases": [], "errors": []}
    report_path = out / "verification.json"

    def save():
        temporary = report_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
        temporary.replace(report_path)

    save()  # Invalidate stale success before reading inputs or launching a command.
    try:
        before = snapshot(root)
        report["inputs"] = before
        save()
        for name, argv, required in PHASES:
            started = time.perf_counter()
            code, output = run(argv, root)
            log = f"{name}.log"
            (out / log).write_text(output)
            missing = [marker for marker in required
                       if not any(line.startswith(marker) for line in output.splitlines())]
            phase = {"name": name, "command": argv, "exitCode": code, "log": log,
                     "logSha256": hashlib.sha256(output.encode()).hexdigest(),
                     "elapsedSeconds": time.perf_counter() - started,
                     "missingMarkers": missing, "passed": code == 0 and not missing}
            report["phases"].append(phase)
            save()
            if not phase["passed"]:
                report["errors"].append(f"verification phase failed: {name}")
                break
        else:
            if snapshot(root) != before:
                report["errors"].append("inputs changed during verification")
            else:
                report["complete"] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["errors"].append(str(error))
    save()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    report = verify(root, root / "out/verification")
    for phase in report["phases"]:
        print(f"{phase['name']}: {'PASS' if phase['passed'] else 'FAIL'} "
              f"({phase['elapsedSeconds']:.2f}s)")
    for error in report["errors"]:
        print(error, file=sys.stderr)
    print("Evidence: out/verification/verification.json")
    return 0 if report["complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
