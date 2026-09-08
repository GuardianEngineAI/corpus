# Contributing

The current pilot supports same-statement replacements with strictly smaller
measured axiom profiles. Proposals for new statements or other witness kinds
need an explicit extension of the ledger and its checks.

## Adding a replacement

1. Add the theorem in the appropriate `Corpus/…` module, following Mathlib's
   naming, documentation, and placement conventions.
2. Add a bridge with checked implication endpoints. The replacement must
   preserve the predecessor's full theorem type and universe parameters.
3. Add a row to `Corpus/Audit.lean`, naming the entry, bridge, predecessor,
   and all three exact axiom profiles.
4. Run the commands in the README, including the adversarial audit fixtures.
5. Open a PR explaining the result and the measured change in assumptions.

The union of the entry and bridge profiles must be a strict subset of the
predecessor's. A bridge cannot hide an assumption that the replacement
claims to remove. Declared profiles must equal the kernel-computed profiles,
and every audited closure must exclude `sorryAx`.

This checks improvement relative to the named predecessor. It does not
establish that no other proof already attains the same profile, or that the
remaining assumptions are necessary. Corpus-wide comparison is a separate
integration obligation.

## Review and attribution

Review helps improve statements, interfaces, explanations, naming, and
placement. Suggestions carry their reasons and scope. Submitter identity
does not enter the mathematical verification criteria; git authorship and
co-author credit remain intact.

The intended merge gate is a trusted verification report for the exact
merge candidate and environment. That operator integration is still being
built. Current CI establishes the checks listed in the README and does not
by itself implement automatic admission.

## Changes to verification policy

Changes to the auditor, toolchain, workflow, or supported witness kinds must
identify the obligation being changed and add a fixture exposing the
failure the change addresses. A proposal cannot establish its own
admissibility by deleting or weakening its checks. The trusted policy and
report-binding mechanism is tracked in the integration roadmap.
