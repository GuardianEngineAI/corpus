/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Init.Data.Option.Lemmas

/-!
# Option lemmas, constructively

Same-statement replacements for core `Option` lemmas whose stock proofs
route through `Classical.choice` (a `simp` step pulls a classical lemma into
the term). The propositions are intuitionistically valid — `Option` is a
concrete inductive with decidable structure — so the reproofs close by case
analysis.

| entry | profile | replaces (stock profile `[propext, Classical.choice, Quot.sound]`) |
|---|---|---|
| `Corpus.Option.eq_none_iff_forall_not_mem` | `∅` | `Option.eq_none_iff_forall_not_mem` |
| `Corpus.Option.bind_eq_none'` | `∅` | `Option.bind_eq_none'` |

Each entry declares its axiom profile; `Corpus/Audit.lean` recomputes entry,
bridge, and predecessor profiles from the kernel environment and fails on any
mismatch or on a narrowing that is not strict. A circular "reproof" that
merely rewrites with the stock lemma inherits the stock profile and is caught
by that audit, never admitted.
-/

universe u

namespace Corpus.Option

/-- Constructive reproof of `Option.eq_none_iff_forall_not_mem`:
an option equals `none` iff no element belongs to it. Same statement as the
core lemma; this proof uses no axioms (the core proof's `simp` routes through
`Classical.choice`). -/
theorem eq_none_iff_forall_not_mem {α : Type u} {o : Option α} :
    o = none ↔ ∀ a, a ∉ o := by
  constructor
  · intro h a ha
    subst h
    exact (Option.not_mem_none a) ha
  · intro h
    cases o with
    | none => rfl
    | some x => exact absurd (Option.mem_some_self x) (h x)

/-- The bridge `new ⊢ old`: from the replacement's statement, the core
lemma's statement follows. The statements are identical, so the bridge is the
identity implication made explicit — but stating it explicitly is what lets
its axiom profile be measured. That profile is `∅`, so the bridge adds
nothing to the replacement's accounting: the strict narrowing is certified by
the reproof itself, never smuggled through the bridge. The hypothesis is the
*type* of the replacement; the conclusion is the *type* of the core lemma;
they coincide, and that coincidence — same proposition, not resemblance — is
exactly what the same-statement admission rule requires. -/
theorem bridge_eq_none_iff_forall_not_mem {α : Type u} {o : Option α}
    (new : o = none ↔ ∀ a, a ∉ o) : o = none ↔ ∀ a, a ∉ o :=
  new

/-- Constructive reproof of `Option.bind_eq_none'`: `o.bind f = none` iff `f`
never maps an element of `o` to `some`. Axiom profile `∅`; the core lemma's
profile is `[propext, Classical.choice, Quot.sound]`. -/
theorem bind_eq_none' {α β : Type u} {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, o = some a → f a ≠ some b := by
  constructor
  · intro h b a hoa hfa
    subst hoa
    rw [Option.bind_some] at h
    rw [hfa] at h
    exact Option.some_ne_none b h
  · intro h
    cases o with
    | none => rfl
    | some a =>
      rw [Option.bind_some]
      cases hf : f a with
      | none => rfl
      | some b => exact absurd hf (h b a rfl)

/-- The bridge `new ⊢ old` for `bind_eq_none'` (same statement; profile `∅`).
See `bridge_eq_none_iff_forall_not_mem` for the rationale. -/
theorem bridge_bind_eq_none' {α β : Type u} {o : Option α} {f : α → Option β}
    (new : o.bind f = none ↔ ∀ b a, o = some a → f a ≠ some b) :
    o.bind f = none ↔ ∀ b a, o = some a → f a ≠ some b :=
  new

end Corpus.Option
