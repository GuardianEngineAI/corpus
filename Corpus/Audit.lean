/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Corpus
import Lean

/-!
# The axiom-profile audit

The second decisive gate (the first is `lake build`, the kernel). For every
ledger row this audit recomputes, from the kernel environment via
`Lean.collectAxioms`:

1. the entry's profile — must equal the declared profile exactly;
2. the bridge's profile — must equal its declared profile exactly;
3. the predecessor's profile — the recorded fact must still hold on this
   toolchain;
4. strict narrowing — the entry's profile must be a *proper* subset of the
   predecessor's (a circular "reproof" that rewrites with the stock lemma
   inherits its profile and fails here);
5. no `sorryAx` anywhere (the kernel-level no-sorry check, superseding any
   source grep).

A coverage pass then asserts every non-auxiliary theorem in the `Corpus`
namespace is ledgered — an entry added to the library but not to the ledger
fails the audit rather than escaping it.

Run: `lake env lean Corpus/Audit.lean` (after `lake build`). Any failure is a
`#eval` error and a nonzero exit; CI treats it as decisive. Declared profiles
live only here — this ledger is the library's profile registry, the single
source the documentation tables must match.
-/

open Lean

namespace Corpus.Audit

/-- One ledger row: an admitted entry, its bridge, the core predecessor it
replaces, and the three declared axiom profiles (sorted dotted names). -/
structure Row where
  entry : Name
  entryProfile : List String
  bridge : Name
  bridgeProfile : List String
  predecessor : Name
  predecessorProfile : List String

/-- The stock profile shared by every predecessor below. -/
def stock : List String := ["Classical.choice", "Quot.sound", "propext"]

/-- The ledger. Extend here when an entry lands; the audit covers every row
and the coverage pass refuses theorems that are not rows. -/
def ledger : List Row :=
  [ { entry := `Corpus.Option.eq_none_iff_forall_not_mem,
      entryProfile := [],
      bridge := `Corpus.Option.bridge_eq_none_iff_forall_not_mem,
      bridgeProfile := [],
      predecessor := `Option.eq_none_iff_forall_not_mem,
      predecessorProfile := stock },
    { entry := `Corpus.Option.bind_eq_none',
      entryProfile := [],
      bridge := `Corpus.Option.bridge_bind_eq_none',
      bridgeProfile := [],
      predecessor := `Option.bind_eq_none',
      predecessorProfile := stock },
    { entry := `Corpus.List.eq_nil_iff_forall_not_mem,
      entryProfile := [],
      bridge := `Corpus.List.bridge_eq_nil_iff_forall_not_mem,
      bridgeProfile := [],
      predecessor := `List.eq_nil_iff_forall_not_mem,
      predecessorProfile := stock },
    { entry := `Corpus.List.filter_eq_nil_iff,
      entryProfile := ["propext"],
      bridge := `Corpus.List.bridge_filter_eq_nil_iff,
      bridgeProfile := [],
      predecessor := `List.filter_eq_nil_iff,
      predecessorProfile := stock },
    { entry := `Corpus.List.countP_eq_zero,
      entryProfile := ["Quot.sound", "propext"],
      bridge := `Corpus.List.bridge_countP_eq_zero,
      bridgeProfile := [],
      predecessor := `List.countP_eq_zero,
      predecessorProfile := stock },
    { entry := `Corpus.List.all_eq_false,
      entryProfile := ["Quot.sound", "propext"],
      bridge := `Corpus.List.bridge_all_eq_false,
      bridgeProfile := [],
      predecessor := `List.all_eq_false,
      predecessorProfile := stock },
    { entry := `Corpus.List.flatten_ne_nil_iff,
      entryProfile := ["Quot.sound", "propext"],
      bridge := `Corpus.List.bridge_flatten_ne_nil_iff,
      bridgeProfile := [],
      predecessor := `List.flatten_ne_nil_iff,
      predecessorProfile := stock },
    { entry := `Corpus.List.findIdx_eq_length,
      entryProfile := ["Quot.sound", "propext"],
      bridge := `Corpus.List.bridge_findIdx_eq_length,
      bridgeProfile := [],
      predecessor := `List.findIdx_eq_length,
      predecessorProfile := stock } ]

/-- The kernel axiom closure of `n`, as sorted dotted names. -/
def profile (n : Name) : CoreM (List String) := do
  let ax ← collectAxioms n
  return (ax.toList.map (·.toString)).mergeSort (· ≤ ·)

def fmt (xs : List String) : String :=
  "[" ++ String.intercalate ", " xs ++ "]"

def subsetOf (a b : List String) : Bool := a.all b.contains

/-- `a` is a proper subset of `b` (as sets of names). -/
def strictlyBelow (a b : List String) : Bool :=
  subsetOf a b && !(subsetOf b a)

/-- All failures for one row (empty = green). -/
def checkRow (r : Row) : CoreM (List String) := do
  let e ← profile r.entry
  let b ← profile r.bridge
  let p ← profile r.predecessor
  let mut fails : List String := []
  if e ≠ r.entryProfile then
    fails := fails ++ [s!"{r.entry}: declared {fmt r.entryProfile} ≠ computed {fmt e}"]
  if b ≠ r.bridgeProfile then
    fails := fails ++ [s!"{r.bridge}: declared {fmt r.bridgeProfile} ≠ computed {fmt b}"]
  if p ≠ r.predecessorProfile then
    fails := fails ++ [s!"{r.predecessor}: recorded {fmt r.predecessorProfile} ≠ computed {fmt p}"]
  unless strictlyBelow e p do
    fails := fails ++ [s!"{r.entry}: profile {fmt e} is not a strict narrowing of {r.predecessor}'s {fmt p}"]
  for prof in [e, b, p] do
    if prof.contains "sorryAx" then
      fails := fails ++ [s!"{r.entry}: sorryAx reachable"]
  if fails.isEmpty then
    IO.println s!"OK {r.entry} {fmt e} ⊂ {r.predecessor} {fmt p}"
  return fails

/-- Auxiliary declarations the coverage pass ignores (matchers, lifted
proofs, compiler-generated structure lemmas) — everything a human did not
name. -/
def isAux (n : Name) : Bool :=
  n.isInternal ||
    match n with
    | .str _ s =>
        s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_" ||
        s == "inj" || s == "injEq" || s == "sizeOf_spec" ||
        s == "noConfusion" || s == "noConfusionType" || s == "eq_def"
    | _ => true

/-- Every non-auxiliary theorem under `Corpus` must be a ledger row (entry or
bridge): the anti-drift guard — content cannot land unledgered. The
`Corpus.Audit` namespace is excluded: the auditor's own machinery is not the
audited library (it is not imported by the library root). -/
def coverage : CoreM (List String) := do
  let env ← getEnv
  let listed := ledger.map (·.entry) ++ ledger.map (·.bridge)
  let mut fails : List String := []
  for (n, ci) in env.constants.toList do
    if (`Corpus).isPrefixOf n && !(`Corpus.Audit).isPrefixOf n && !isAux n then
      if let .thmInfo _ := ci then
        unless listed.contains n do
          fails := fails ++ [s!"unledgered theorem: {n}"]
  return fails

def audit : CoreM Unit := do
  let mut fails : List String := []
  for r in ledger do
    fails := fails ++ (← checkRow r)
  fails := fails ++ (← coverage)
  if fails.isEmpty then
    IO.println s!"audit green: {ledger.length} entries, every profile declared = computed, every narrowing strict, coverage total"
  else
    throwError ("audit FAILED:\n" ++ String.intercalate "\n" fails)

#eval audit

end Corpus.Audit
