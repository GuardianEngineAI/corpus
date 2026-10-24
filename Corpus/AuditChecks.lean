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
theorem twoFactPredecessor : True := (⟨predecessorFact, additionalFact⟩ : True ∧ True).1

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

open Lean in
/-- A declared profile is compared as the kernel computes it, sorted. Written
order is not evidence, but a missing or repeated name still is. -/
def checkProfileOrder : CoreM Unit := do
  let qualify (n : Name) := `Corpus.Audit.Checks ++ n
  let fixture ← row (qualify `entry) (qualify `identityBridge) (qualify `twoFactPredecessor)
  let computed := fixture.predecessorProfile
  unless computed.length == 2 do
    throwError "profile-order fixture needs a two-axiom predecessor, computed {computed}"
  let reversed := computed.reverse
  if reversed == computed then
    throwError "profile-order fixture did not reorder {computed}"
  let reorderedFailures ← checkRow { fixture with predecessorProfile := reversed }
  unless reorderedFailures.isEmpty do
    throwError "accurately declared profile rejected for its order: {reorderedFailures}"
  let wrong : List (String × List String) :=
    [ ("missing name", reversed.take 1),
      ("repeated name", reversed ++ reversed.take 1) ]
  let mut accepted : Array String := #[]
  for (label, declared) in wrong do
    if (← checkRow { fixture with predecessorProfile := declared }).isEmpty then
      accepted := accepted.push label
  unless accepted.isEmpty do
    throwError "inaccurately declared profiles accepted: {accepted}"
  IO.println s!"public profile-order checks: reordered profile accepted, {wrong.length} inaccurate profiles rejected"

#eval checkProfileOrder

end Corpus.Audit.Checks
