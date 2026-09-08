"""Exercise the actual CI test command under GitHub's implicit bash -e shell."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class WorkflowTests(unittest.TestCase):
    def test_failed_runner_tests_cannot_be_hidden_by_tee(self):
        root = Path(__file__).resolve().parent.parent
        lines = (root / ".github/workflows/ci.yml").read_text().splitlines()
        start = lines.index("      - name: Verification runner contract tests")
        self.assertEqual(lines[start + 1], "        run: |")
        command = []
        for line in lines[start + 2:]:
            if not line.startswith("          "):
                break
            command.append(line[10:])
        self.assertTrue(command)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            binary = work / "bin"
            binary.mkdir()
            fake_python = binary / "python3"
            fake_python.write_text("#!/bin/sh\nexit 23\n")
            fake_python.chmod(0o755)
            result = subprocess.run(
                ["bash", "-e", "-c", "\n".join(command)], cwd=work,
                env={**os.environ, "PATH": str(binary) + os.pathsep + os.environ["PATH"]},
                capture_output=True, text=True, check=False, timeout=10,
            )
        self.assertEqual(result.returncode, 23, "tee hid the failing test command")


if __name__ == "__main__":
    unittest.main()
