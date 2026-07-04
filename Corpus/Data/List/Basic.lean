/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Init.Data.List.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Count
import Init.Data.List.Find
import Init.Data.Bool
import Init.SimpLemmas

/-!
# List lemmas, constructively

Same-statement replacements for core `List` lemmas whose stock proofs route
through `Classical.choice` (a `simp` step pulls a classical lemma into the
term). The propositions are intuitionistically valid — `List` is a concrete
inductive with decidable structure — so the reproofs close by case analysis
and induction.

Stock profile of every predecessor below: `[propext, Classical.choice, Quot.sound]`.

| entry | profile | dropped vs the core lemma |
|---|---|---|
| `Corpus.List.eq_nil_iff_forall_not_mem` | `∅` | propext, choice, Quot.sound |
| `Corpus.List.filter_eq_nil_iff` | `[propext]` | choice, Quot.sound |
| `Corpus.List.countP_eq_zero` | `[propext, Quot.sound]` | choice |
| `Corpus.List.all_eq_false` | `[propext, Quot.sound]` | choice |
| `Corpus.List.flatten_ne_nil_iff` | `[propext, Quot.sound]` | choice |
| `Corpus.List.findIdx_eq_length` | `[propext, Quot.sound]` | choice |

`propext` and `Quot.sound` are foundational (they enter through the core
membership/count lemmas the reproofs reuse), not classical — every entry is a
*strict* narrowing of its predecessor's profile, dropping `Classical.choice`
in all cases and additionally `propext`/`Quot.sound` where the reproof avoids
the core lemmas that carry them. Each profile is pinned to exactly what the
kernel computes (`Corpus/Audit.lean` fails on any drift); nothing is hardened
to "axiom-free" that is not.
-/

universe u

namespace Corpus.List

/-- Constructive reproof of `List.eq_nil_iff_forall_not_mem`: a list is empty
iff no element belongs to it. Axiom profile `∅`; the core lemma's profile is
`[propext, Classical.choice, Quot.sound]`. -/
theorem eq_nil_iff_forall_not_mem {α : Type u} {l : List α} :
    l = [] ↔ ∀ a, a ∉ l := by
  constructor
  · intro h a ha
    subst h
    exact List.not_mem_nil ha
  · intro h
    cases l with
    | nil => rfl
    | cons x xs => exact absurd List.mem_cons_self (h x)

/-- The bridge `new ⊢ old` for `eq_nil_iff_forall_not_mem` (same statement;
profile `∅`). The bridge is the identity implication made explicit so its
axiom profile is measurable; the strict narrowing is certified by the reproof
itself, never smuggled through the bridge. -/
theorem bridge_eq_nil_iff_forall_not_mem {α : Type u} {l : List α}
    (new : l = [] ↔ ∀ a, a ∉ l) : l = [] ↔ ∀ a, a ∉ l :=
  new

/-- Constructive reproof of `List.filter_eq_nil_iff`: `filter p l = []` iff no
element of `l` satisfies `p`. Axiom profile `[propext]` — the `propext` enters
through the core membership/filter lemmas reused (`List.mem_filter`,
`List.filter_cons`), not from choice. Strict narrowing of the core lemma's
`[propext, Classical.choice, Quot.sound]`: `Classical.choice` and `Quot.sound`
eliminated. -/
theorem filter_eq_nil_iff {α : Type u} {p : α → Bool} {l : List α} :
    List.filter p l = [] ↔ ∀ a ∈ l, ¬ p a = true := by
  constructor
  · intro h a ha hp
    have hmem : a ∈ List.filter p l := List.mem_filter.mpr ⟨ha, hp⟩
    rw [h] at hmem
    exact List.not_mem_nil hmem
  · intro h
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.filter_cons]
      by_cases hx : p x = true
      · exact absurd hx (h x List.mem_cons_self)
      · rw [if_neg hx]
        exact ih (fun a ha => h a (List.mem_cons_of_mem x ha))

/-- The bridge `new ⊢ old` for `filter_eq_nil_iff` (same statement; profile
`∅`, which is `⊆` the entry's own). See `bridge_eq_nil_iff_forall_not_mem`
for the rationale. -/
theorem bridge_filter_eq_nil_iff {α : Type u} {p : α → Bool} {l : List α}
    (new : List.filter p l = [] ↔ ∀ a ∈ l, ¬ p a = true) :
    List.filter p l = [] ↔ ∀ a ∈ l, ¬ p a = true :=
  new

/-- Constructive reproof of `List.countP_eq_zero`: `countP p l = 0` iff no
element of `l` satisfies `p`. Axiom profile `[propext, Quot.sound]` — both
enter through the core list lemmas reused (`List.mem_cons`,
`List.countP_cons`), not from choice. Strict narrowing of the core lemma's
`[propext, Classical.choice, Quot.sound]`: `Classical.choice` eliminated. -/
theorem countP_eq_zero {α : Type u} {l : List α} {p : α → Bool} :
    List.countP p l = 0 ↔ ∀ a ∈ l, ¬ p a = true := by
  induction l with
  | nil =>
    constructor
    · intro _ a ha
      exact absurd ha List.not_mem_nil
    · intro _
      rfl
  | cons x xs ih =>
    rw [List.countP_cons]
    constructor
    · intro h a ha
      by_cases hx : p x = true
      · rw [if_pos hx] at h
        omega
      · rw [if_neg hx, Nat.add_zero] at h
        rcases List.mem_cons.mp ha with rfl | hmem
        · exact hx
        · exact ih.mp h a hmem
    · intro h
      have hx : ¬ p x = true := h x List.mem_cons_self
      rw [if_neg hx, Nat.add_zero]
      exact ih.mpr (fun a ha => h a (List.mem_cons_of_mem x ha))

/-- The bridge `new ⊢ old` for `countP_eq_zero` (same statement; profile `∅`).
See `bridge_eq_nil_iff_forall_not_mem` for the rationale. -/
theorem bridge_countP_eq_zero {α : Type u} {l : List α} {p : α → Bool}
    (new : List.countP p l = 0 ↔ ∀ a ∈ l, ¬ p a = true) :
    List.countP p l = 0 ↔ ∀ a ∈ l, ¬ p a = true :=
  new

/-- Constructive reproof of `List.all_eq_false`: `l.all p = false` iff some
element of `l` fails `p`. Axiom profile `[propext, Quot.sound]` (from the core
`List.all_cons`/`Bool` lemmas reused), a strict narrowing of the predecessor's
`[propext, Classical.choice, Quot.sound]` — `Classical.choice` eliminated. -/
theorem all_eq_false {α : Type u} {p : α → Bool} {l : List α} :
    l.all p = false ↔ ∃ x ∈ l, ¬ p x = true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.all_cons]
    constructor
    · intro h
      rcases Bool.and_eq_false_iff.mp h with hx | hrest
      · exact ⟨x, List.mem_cons_self, by rw [hx]; simp⟩
      · rcases ih.mp hrest with ⟨y, hy, hpy⟩
        exact ⟨y, List.mem_cons_of_mem x hy, hpy⟩
    · rintro ⟨y, hy, hpy⟩
      rcases List.mem_cons.mp hy with rfl | hmem
      · have hy' : p y = false := Bool.not_eq_true _ |>.mp hpy
        rw [hy']; simp
      · have hrest : xs.all p = false := ih.mpr ⟨y, hmem, hpy⟩
        rw [hrest]; simp

/-- The bridge `new ⊢ old` for `all_eq_false` (same statement; profile `∅`).
See `bridge_eq_nil_iff_forall_not_mem` for the rationale. -/
theorem bridge_all_eq_false {α : Type u} {p : α → Bool} {l : List α}
    (new : l.all p = false ↔ ∃ x ∈ l, ¬ p x = true) :
    l.all p = false ↔ ∃ x ∈ l, ¬ p x = true :=
  new

/-- Constructive reproof of `List.flatten_ne_nil_iff`: a flattened list is
nonempty iff some inner list is nonempty. Axiom profile `[propext, Quot.sound]`
(from the core `List.flatten_cons`/`append`/`mem` lemmas reused), a strict
narrowing of the predecessor's `[propext, Classical.choice, Quot.sound]` —
`Classical.choice` eliminated. -/
theorem flatten_ne_nil_iff {α : Type u} {xss : List (List α)} :
    xss.flatten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ [] := by
  induction xss with
  | nil => simp
  | cons ys yss ih =>
    rw [List.flatten_cons]
    constructor
    · intro h
      cases ys with
      | nil =>
        rw [List.nil_append] at h
        rcases ih.mp h with ⟨xs, hxs, hne⟩
        exact ⟨xs, List.mem_cons_of_mem _ hxs, hne⟩
      | cons z zs => exact ⟨z :: zs, List.mem_cons_self, by simp⟩
    · rintro ⟨xs, hxs, hne⟩
      rcases List.mem_cons.mp hxs with rfl | hmem
      · intro hcontra
        rw [List.append_eq_nil_iff] at hcontra
        exact hne hcontra.1
      · intro hcontra
        rw [List.append_eq_nil_iff] at hcontra
        exact (ih.mpr ⟨xs, hmem, hne⟩) hcontra.2

/-- The bridge `new ⊢ old` for `flatten_ne_nil_iff` (same statement; profile
`∅`). See `bridge_eq_nil_iff_forall_not_mem` for the rationale. -/
theorem bridge_flatten_ne_nil_iff {α : Type u} {xss : List (List α)}
    (new : xss.flatten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []) :
    xss.flatten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ [] :=
  new

/-- Constructive reproof of `List.findIdx_eq_length`: `findIdx p xs` runs off
the end iff no element satisfies `p`. Axiom profile `[propext, Quot.sound]`
(from the core `List.findIdx_cons`/`mem` lemmas reused), a strict narrowing of
the predecessor's `[propext, Classical.choice, Quot.sound]` —
`Classical.choice` eliminated. -/
theorem findIdx_eq_length {α : Type u} {p : α → Bool} {xs : List α} :
    List.findIdx p xs = xs.length ↔ ∀ x ∈ xs, p x = false := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    rw [List.findIdx_cons, List.length_cons]
    by_cases hpa : p a = true
    · simp only [hpa, cond_true]
      constructor
      · intro h; omega
      · intro h; exact absurd (h a List.mem_cons_self) (by simp [hpa])
    · have hpa' : p a = false := by simp_all
      simp only [hpa', cond_false]
      constructor
      · intro h x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hpa'
        · exact ih.mp (by omega) x hmem
      · intro h
        have hlen : List.findIdx p as = as.length :=
          ih.mpr (fun x hx => h x (List.mem_cons_of_mem a hx))
        omega

/-- The bridge `new ⊢ old` for `findIdx_eq_length` (same statement; profile
`∅`). See `bridge_eq_nil_iff_forall_not_mem` for the rationale. -/
theorem bridge_findIdx_eq_length {α : Type u} {p : α → Bool} {xs : List α}
    (new : List.findIdx p xs = xs.length ↔ ∀ x ∈ xs, p x = false) :
    List.findIdx p xs = xs.length ↔ ∀ x ∈ xs, p x = false :=
  new

end Corpus.List
