# Contributing

A contribution is a pull request containing Lean source and a declared axiom
profile. Nothing about who you are enters admission; everything about what
you wrote does.

## What gates (decisive checks)

A PR merges when these are green, and only these:

1. **Kernel** — `lake build` succeeds; every proof elaborates and
   kernel-checks. No `sorry` (the audit checks `sorryAx` reachability at the
   kernel level, so a `sorry` hidden behind a helper still fails).
2. **Profile** — the axiom profile you declare in the audit ledger
   (`Corpus/Audit.lean`) equals the kernel-computed one, exactly. Disclosed
   axioms are legibility, not sin: an exotic-but-declared axiom does not
   reject; an *undeclared* one always does, because the declaration is
   false.
3. **Strict narrowing** (same-statement replacements only) — a replacement
   for an existing lemma is admitted exactly when it proves the identical
   proposition with a strictly smaller axiom profile, certified by a bridge
   theorem whose own profile adds nothing. Equal-or-worse on every measured
   axis is a duplicate, not a contribution.
4. **Ledger coverage** — every theorem you add is a row in the audit ledger.
   Content cannot land unledgered.
5. **Corpus checks** (operator-side) — novelty, statement-level duplicates,
   and name collisions against the certified corpus store; the verification
   report is posted to the PR. A name the corpus already binds to different
   content cannot merge under that name — renaming fixes it.

## What never gates

Lint findings, style and naming suggestions, statement-shape near-match
notices, and any judgment of interestingness or importance. These surface on
the PR as material for revision and for ranking — they are channels, not
gates. Reviewers comment, suggest concrete edits, and route attention; a
review cannot veto green checks and cannot approve past red ones.

## Conventions

Mathlib's conventions apply wholesale: naming, docstrings and module docs,
file layout, deprecation practice. Every new declaration carries a docstring
stating what it proves and, for replacements, the predecessor and both
profiles. Copyright headers name the human authors — attribution is visible
by design.

## Adding an entry, concretely

1. Put the theorem in the right `Corpus/…` file (Mathlib-style placement).
2. For a same-statement replacement: add the bridge theorem beside it.
3. Add the ledger row in `Corpus/Audit.lean` with the declared profiles.
4. `lake build && lake env lean Corpus/Audit.lean` — both green locally.
5. Open the PR; the template asks for the declared profile and (for
   replacements) the predecessor. It does not ask who you are.
