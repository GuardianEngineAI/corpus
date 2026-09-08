# Testing and verification

A change states its contract and witness level before implementation. For a
behavior change, add the smallest regression that exposes the missing or wrong
behavior, run it, and retain the expected failure. Implement the change, rerun
that same test unchanged, then run the affected suites. Refactor while preserving
those results.

A missing import or syntax error is an interface or compilation failure. It does
not substitute for an executable assertion failing for the intended behavioral
reason. For a new API, a deliberate executable stub may establish the initial
behavioral RED; label that setup explicitly. A retrospective mutation check
shows that today's suite detects a broken guard; it does not establish that the
original implementation was written test-first.

## Required evidence for behavior or verification-policy changes

Record the contract being changed, witness level, baseline revision, test-source
hash, exact focused command, expected failure, observed RED result and log hash,
implementation revision or source hashes, unchanged-test GREEN, and relevant
suite results. State exclusions rather than treating skipped work as passed.
The PR template asks for this record; CI retains its own execution evidence.
A completed checklist is not itself proof of development chronology.

## Local and hosted commands

Python 3.10+ and the pinned Lean toolchain are sufficient; the Python runner uses
only the standard library.

```sh
python3 -B -m unittest discover -s tests -v
python3 -B scripts/verify.py
```

CI runs those same commands. The runner builds both library targets, builds the
auditor, checks theorem relations/profiles/coverage, and runs the adversarial
fixtures. A failed command or missing success marker makes the runner fail.
Its report cannot retain a previous run's success after a new failure. Source
files are hashed before and after the run; a changed snapshot invalidates the
result. The checkout revision is recorded separately from actual file hashes,
so uncommitted work is not represented as the committed tree.

Reports and phase logs are written to `out/verification/`; the workflow retains
`out/` for 14 days, including failed-run evidence when files are available. This
is repository CI evidence, not the separate trusted operator admission receipt.
Source inventory excludes `.git`, `.lake`, `out`, and Python bytecode; it does
not attest every toolchain binary or independently authenticate the workflow.

## Coverage and failure sensitivity

Tests exercise valid replacements, wrong theorem/bridge endpoints, retained or
added bridge assumptions, unledgered theorem coverage, and the verification
runner's failure handling. Each new admission or preservation rule needs a
positive example and a counterexample that the rule rejects. Supporting
compiler theorems have explicit owners and coverage checks; generated-looking
names do not establish an exemption.

The engineering project also runs Python package gates, encoding vectors,
independent Lean/archive agreement, reconstruction and byte round trips, and
resource/invariance fixtures. Those private suites are not implicitly claimed
by this public repository's CI. Corpus-wide and additional witness-kind checks
remain separate registered obligations.

Keep workflow permissions read-only, actions pinned to exact commits, and build
caches disabled in this small certification pilot. Do not run untrusted PR code
in a privileged workflow. Cancellation of superseded runs saves work; a cancelled
run is not a pass. Automatic merge remains disabled until trusted policy and
exact merge-content binding are implemented.
