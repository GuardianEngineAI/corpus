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

## Checklist

- [ ] `lake build` green locally
- [ ] `lake env lean Corpus/Audit.lean` green locally (ledger row added)
- [ ] `lake build Corpus.Audit && lake env lean Corpus/AuditChecks.lean` green
- [ ] Docstrings state the result and, for replacements, both profiles
- [ ] Naming and placement follow Mathlib conventions
