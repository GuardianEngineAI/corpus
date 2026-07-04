# corpus

> Working name. A formal mathematics library whose admission is decisive
> checks — kernel verification and axiom-profile legibility — never the
> standing of who produced a contribution.

Generation of formal mathematics now outruns human review. This library is
infrastructure for that regime: every admission criterion is a check a
machine runs, every check's result is recomputable by anyone holding the
sources, and identity is structurally not an input to any of it. The goal is
a library that grows faster than human review while carrying *more*
certainty, not less.

## How admission works

A contribution is a pull request. Two gates run on every PR, both decisive,
both recomputable:

| gate | what it decides | how |
|---|---|---|
| kernel | the proofs are proofs | `lake build` (Lean 4 kernel) |
| profile | the declared axiom profile is the computed one | `lake env lean Corpus/Audit.lean` |

The audit recomputes every declared axiom profile from the kernel
environment (`Lean.collectAxioms`), verifies each same-statement replacement
strictly narrows its predecessor's profile, checks `sorryAx` is unreachable,
and refuses any theorem present in the library but absent from the ledger.
A merge follows green checks. Reviewers comment, suggest, and route — review
improves artifacts; it does not hold a veto that overrides green checks, and
there is no approval that overrides red ones.

Checks that need the certified corpus store (novelty against the full
library, statement-level duplicate detection, name-collision joins,
statement-shape near-matches) run operator-side and post their verification
report to the PR. They are the same discipline at larger scale: computed,
recomputable, identity-blind.

**Identity and attribution.** Who submitted a PR is never an input to
admission. Who wrote the mathematics is permanently recorded — git history
and per-file author lines stand untouched. Blindness governs the verdict,
never the byline.

## What is in the library (v0)

Eight same-statement constructive replacements for Lean-core lemmas whose
stock proofs route through `Classical.choice`. Each entry proves the
*identical* proposition with a strictly smaller kernel-computed axiom
profile; the stock profile of every predecessor is
`[propext, Classical.choice, Quot.sound]`.

| entry | profile |
|---|---|
| `Corpus.Option.eq_none_iff_forall_not_mem` | `∅` |
| `Corpus.Option.bind_eq_none'` | `∅` |
| `Corpus.List.eq_nil_iff_forall_not_mem` | `∅` |
| `Corpus.List.filter_eq_nil_iff` | `[propext]` |
| `Corpus.List.countP_eq_zero` | `[propext, Quot.sound]` |
| `Corpus.List.all_eq_false` | `[propext, Quot.sound]` |
| `Corpus.List.flatten_ne_nil_iff` | `[propext, Quot.sound]` |
| `Corpus.List.findIdx_eq_length` | `[propext, Quot.sound]` |

Every profile in this table is enforced by the audit — the table cannot
silently drift from what the kernel computes. `Counterexamples/` is a
first-class build target from day one: refutations, independence witnesses,
and profile-witness pairs face the same checks as everything else.

## Relation to Mathlib

This library adopts [Mathlib](https://github.com/leanprover-community/mathlib4)'s
conventions wholesale — naming, docstring and module-doc style, deprecation
discipline, CI shape — and is built to be complementary infrastructure, not
a fork and not a competitor. It diverges in exactly five places, each on
purpose:

1. **Axiom-profile disclosure is first-class** — every declaration carries
   its measured profile, and the audit holds declared equal to computed.
2. **Admission is by decisive checks**, with review as a channel that
   improves artifacts rather than a gate that decides them.
3. **Same-statement replacements are admitted on strict, measured
   improvement** — today's axis: a strictly smaller axiom profile.
4. **Content-addressed identity beneath the names** — the certified store is
   the authority; `.lean` files are its presentation.
5. **Blind adjudication, visible attribution** — identity absent from
   admission, present in credit.

## Building

```
lake build                        # the kernel gate
lake env lean Corpus/Audit.lean   # the profile gate
```

Toolchain is pinned in `lean-toolchain`; there are no dependencies.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). License:
[Apache 2.0](LICENSE).
