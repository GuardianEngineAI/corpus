# Integration roadmap

Each increment closes a named verification obligation and includes a
reproducible check. Source size and generated theorem count are descriptive
measurements, not progress criteria.

## Trustworthy contribution loop

- Bind the operator report to the exact contribution, merge base, corpus
  snapshot, toolchain, and verification-policy revision. Replays after any
  change must fail; changing a PR's workflow must not manufacture admission.
- Join replacements against the known statement/profile frontier. A proof
  already matched or dominated by an existing profile must not earn new
  corpus-progress credit by naming a worse predecessor.
- Make archive accession and release export reproduce the admitted content
  and reports. A round trip must preserve statement identity, declared
  assumptions, and witness kind.
- Run these checks on the merge candidate before enabling automated merge.

## Principled proof comparisons

- Keep observed axiom profiles as a partial order. Equal and incomparable
  profiles have explicit outcomes; profile inclusion is not axiom necessity.
- Account for transitive dependency support under a named background before
  using proof size for admission. Aliases and helper extraction must not
  manufacture progress, and shared dependencies must be counted consistently.
- Add computational or structural witness kinds only with explicit
  transformations and preservation obligations.

## Automation that saves review work

- Reuse Mathlib's lint, import analysis, documentation, and queue tooling.
- Choose one recurring review pattern, produce suggested repairs, and
  recheck the changed artifact. Measure correct suggestions, verified
  repairs, and review effort saved on a held-out set.
- Generate declaration documentation linked to the corresponding
  statement, assumption, and comparison records.
- Exercise dependency updates on a second pinned Lean/Mathlib snapshot,
  including downstream compatibility checks and reproducible releases.
