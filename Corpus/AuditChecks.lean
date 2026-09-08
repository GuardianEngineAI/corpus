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

namespace CorpusAuditChecks

open Corpus.Audit

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
  let qualify (n : Name) := `CorpusAuditChecks ++ n
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
/-- Coverage must inspect theorem declarations, not infer an exemption from
their spelling. Every probe is kernel-checked in a discarded environment;
the reserved and numeric names exercise the environment-level boundary. -/
def checkCoverage : CoreM Unit := do
  let baseline ← coverage
  unless baseline.isEmpty do
    throwError "coverage fixture baseline is not clean: {baseline}"
  let names : List Name :=
    [ `Corpus.CoverageProbe.ordinary,
      `Corpus.CoverageProbe._unledgered,
      `Corpus.CoverageProbe.proof_unledgered,
      `Corpus.CoverageProbe.match_unledgered,
      `Corpus.CoverageProbe.inj,
      `Corpus.CoverageProbe.injEq,
      `Corpus.CoverageProbe.sizeOf_spec,
      `Corpus.CoverageProbe.noConfusion,
      `Corpus.CoverageProbe.noConfusionType,
      `Corpus.CoverageProbe.eq_def,
      .num `Corpus.CoverageProbe 7,
      `Corpus.Audit.unledgered ]
  let mut omitted : Array Name := #[]
  for name in names do
    let failures ← withoutModifyingEnv do
      addDecl (.thmDecl {
        name, levelParams := [], type := mkConst ``True,
        value := mkConst ``True.intro })
      coverage
    unless failures == [s!"unledgered theorem: {name}"] do
      omitted := omitted.push name
  unless omitted.isEmpty do
    throwError "coverage omitted kernel-checked unledgered theorems: {omitted}"
  IO.println s!"public coverage checks: {names.length} unledgered theorem names rejected"

#eval checkCoverage

open Lean in
/-- Explicit registration must not hide an unrelated theorem. Its empty
axiom profile alone cannot establish a supporting dependency. -/
def checkSupportingCoverage : CoreM Unit := do
  let owner := `Corpus.Option.eq_none_iff_forall_not_mem
  let helper := `Corpus.CoverageProbe.unreachedHelper
  let failures ← withoutModifyingEnv do
    addDecl (.thmDecl {
      name := helper, levelParams := [], type := mkConst ``True,
      value := mkConst ``True.intro })
    coverage ((owner, helper) :: supportingTheorems)
  unless failures.contains s!"supporting theorem is not directly referenced by owner: {owner} -> {helper}" do
    throwError "coverage accepted a forged supporting registration: {failures}"
  IO.println "public supporting coverage checks: forged unrelated registration rejected"

#eval checkSupportingCoverage

end CorpusAuditChecks
