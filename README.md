# corpus

A Lean library pilot for accumulating verified improvements with explicit
statements, witnesses, and axiom dependencies. Contributions are assessed
through their mathematical content; authorship remains visible in git history.

The current package contains eight replacements for Lean-core lemmas, their
bridge theorems, and a reproducible audit. It uses Lean's pinned toolchain and
has no package dependencies.

## What the checks establish

| Check | Evidence and scope |
|---|---|
| Kernel build | The declarations elaborate in the pinned Lean environment. |
| Same statement | Replacement and predecessor theorem types are definitionally equal, with universally quantified parameters aligned. |
| Bridge | The named bridge has the checked implication endpoints, globally or under shared parameters. |
| Assumptions | Declared profiles equal `Lean.collectAxioms` results; replacement **and bridge together** strictly narrow the predecessor's profile. |
| No admitted holes | `sorryAx` is absent from the audited axiom closures. |
| Ledger coverage | Non-auxiliary library theorems must be named in the audit ledger. |

`same-statement` is a specific witness kind. It establishes correspondence of
theorem types in this environment. Computational witness preservation,
logical equivalence between different statements, and axiom necessity each
require their own evidence. Axiom profiles describe the supplied proofs;
they do not establish the weakest possible foundations of the statements.

The audit includes negative fixtures for unrelated statements and bridges,
and for bridges that retain or add assumption dependencies.

## The initial mathematics

All predecessors below have the recorded profile
`[Classical.choice, Quot.sound, propext]`. The source ledger in
`Corpus/Audit.lean` is authoritative for declared profiles.

| Replacement | Entry profile |
|---|---|
| `Corpus.Option.eq_none_iff_forall_not_mem` | `∅` |
| `Corpus.Option.bind_eq_none'` | `∅` |
| `Corpus.List.eq_nil_iff_forall_not_mem` | `∅` |
| `Corpus.List.filter_eq_nil_iff` | `[propext]` |
| `Corpus.List.countP_eq_zero` | `[propext, Quot.sound]` |
| `Corpus.List.all_eq_false` | `[propext, Quot.sound]` |
| `Corpus.List.flatten_ne_nil_iff` | `[propext, Quot.sound]` |
| `Corpus.List.findIdx_eq_length` | `[propext, Quot.sound]` |

## Reproduce the checks

```sh
lake build
lake build Corpus.Audit
lake env lean Corpus/Audit.lean
lake env lean Corpus/AuditChecks.lean
```

CI runs these checks with the pinned toolchain. `Counterexamples` is a
first-class build target. Test-only axioms live in the audit fixtures and
are not imported by the library root.

## Building the contribution loop

This pilot checks replacements against named predecessors. Corpus-wide
novelty and proof-frontier comparison, archive accession, generated docs,
and a trusted operator report bound to the exact merge candidate are
integration work. Automated admission and merge depend on completing that
loop; a green run of contributor-editable CI alone is not its authority.

Proof size is useful descriptive information. A short reference can hide a
large dependency, so body size alone does not establish a better proof.
Comparisons must identify the statement, witness kind, environment, measured
resources, and any unresolved obligations. Incomparable results remain
available for comparison.

We follow [Mathlib's conventions](https://leanprover-community.github.io/contribute/index.html)
and reuse [Lean's CI action](https://github.com/leanprover/lean-action).
The project complements the existing Lean ecosystem through explicit
verification and comparison records. Further Mathlib lint, documentation,
and import tooling belong in the integration plan.

See [CONTRIBUTING.md](CONTRIBUTING.md) and [the integration roadmap](ROADMAP.md).
License: [Apache 2.0](LICENSE).
