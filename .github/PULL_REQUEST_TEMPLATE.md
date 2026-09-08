<!-- Nothing here asks who you are. Everything here is about the artifact. -->

## Summary

<!-- What this adds or replaces, in one or two sentences. -->

## Declared axiom profile

<!-- Per new theorem, the exact profile you added to the Corpus/Audit.lean
     ledger, e.g. `[]` or `[propext, Quot.sound]`. CI recomputes these from
     the kernel; a mismatch fails. -->

## Replaces (same-statement replacements only)

<!-- Predecessor name + its recorded profile. State witness kind
     `same-statement`; the entry and bridge together must strictly narrow
     its profile while preserving its full theorem type and universes. -->

## Test-first evidence

<!-- Contract/witness level; baseline revision; added-test hash and exact command;
     expected and observed RED; same-test GREEN; affected suites. Link logs.
     Distinguish behavioral failures from import/type/compile failures. For new
     APIs, label an executable-stub RED; label retrospective mutation checks.
     Record unavailable checks explicitly. See TESTING.md. -->

## Checklist

- [ ] Expected behavioral RED and unchanged-test GREEN recorded
- [ ] `python3 -B -m unittest discover -s tests -v` green
- [ ] `python3 -B scripts/verify.py` green; report and phase logs inspected
- [ ] Affected suites and any unavailable checks identified
- [ ] Docstrings state the result and, for replacements, both profiles
- [ ] Naming and placement follow Mathlib conventions
