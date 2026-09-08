/-
Copyright (c) 2026 Larsen James Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen James Close
-/
import Corpus.Audit

/-!
# Admission boundary checks

These fixtures exercise the public audit with well-typed declarations and
accurately declared profiles. The two axioms below are adversarial test inputs,
not dependencies of the library or its admitted entries. This module is never
imported by `Corpus`.
-/

namespace Corpus.Audit.Checks

axiom predecessorFact : True
axiom additionalFact : True

theorem entry : True := True.intro
theorem predecessor : True := predecessorFact
theorem identityBridge (h : True) : True := h
theorem unrelatedPredecessor : True ∧ True := ⟨predecessorFact, predecessorFact⟩
theorem unrelatedBridge (h : False) : False := h
theorem retainsDebtBridge (_h : True) : True := predecessorFact
theorem addsDebtBridge (_h : True) : True := additionalFact

open Lean in
/-- Build an accurately disclosed fixture; wrong endpoints cannot hide behind
a deliberately incorrect profile declaration. -/
def row (entry bridge predecessor : Name) : CoreM Row := do
  return {
    entry, entryProfile := ← profile entry,
    bridge, bridgeProfile := ← profile bridge,
    predecessor, predecessorProfile := ← profile predecessor }

open Lean in
def checkAdmission : CoreM Unit := do
  let qualify (n : Name) := `Corpus.Audit.Checks ++ n
  let good ← row (qualify `entry) (qualify `identityBridge) (qualify `predecessor)
  let goodFailures ← checkRow good
  unless goodFailures.isEmpty do
    throwError "valid public replacement rejected: {goodFailures}"
  let bad : List (String × Name × Name) :=
    [ ("unrelated predecessor", `identityBridge, `unrelatedPredecessor),
      ("unrelated bridge", `unrelatedBridge, `predecessor),
      ("bridge retains predecessor debt", `retainsDebtBridge, `predecessor),
      ("bridge adds an axiom", `addsDebtBridge, `predecessor) ]
  let mut accepted : Array String := #[]
  for (label, bridge, target) in bad do
    let fixture ← row (qualify `entry) (qualify bridge) (qualify target)
    let passed ← try
      pure (← checkRow fixture).isEmpty
    catch error =>
      let message ← error.toMessageData.toString
      unless message.startsWith "same-statement " do throw error
      pure false
    if passed then accepted := accepted.push label
  unless accepted.isEmpty do
    throwError "invalid public replacements accepted: {accepted}"
  IO.println s!"public admission checks: 1 valid case accepted, {bad.length} invalid cases rejected"

#eval checkAdmission

end Corpus.Audit.Checks
