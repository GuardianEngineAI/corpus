<!-- Nothing here asks who you are. Everything here is about the artifact. -->

## Summary

<!-- What this adds or replaces, in one or two sentences. -->

## Declared axiom profile

<!-- Per new theorem, the exact profile you added to the Corpus/Audit.lean
     ledger, e.g. `[]` or `[propext, Quot.sound]`. CI recomputes these from
     the kernel; a mismatch fails. -->

## Replaces (same-statement replacements only)

<!-- Predecessor name + its recorded profile. The entry must strictly narrow
     it, certified by the bridge theorem beside your entry. -->

## Checklist

- [ ] `lake build` green locally
- [ ] `lake env lean Corpus/Audit.lean` green locally (ledger row added)
- [ ] Docstrings state the result and, for replacements, both profiles
- [ ] Naming and placement follow Mathlib conventions
