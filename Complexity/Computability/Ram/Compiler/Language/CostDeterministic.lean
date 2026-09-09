/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Determinism of source execution costs

The same source statement and entry state determine its backend-derived count.
Word width, call capacity and the proofs used to realize the execution do not
affect that count. Source execution determinism aligns intermediate states and
the actual callee final state and return before the structural cost rules are compared.

This result requires neither a machine representation nor positive word width.
It compares existing cost observations and does not assert source termination.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ExecutionCost

private theorem observations_eq {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w w' depth depth' : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish finish' : Complexity.Language.State Γ} {control control' : Control result}
    {execution : RealizedExec program w depth stmt entry finish control}
    {execution' : RealizedExec program w' depth' stmt entry finish' control'}
    {steps steps' : Nat} (_ : ExecutionCost execution steps)
    (_ : ExecutionCost execution' steps') : finish = finish' ∧ control = control' :=
  execution.erase.deterministic execution'.erase

/-- A deterministic source trace has one compiled core count, independently of
word width, call capacity, final-state witnesses and realization proofs. -/
theorem deterministic {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec program w depth stmt entry finish control} {steps : Nat}
    (first : ExecutionCost execution steps) :
    ∀ {w' depth' : Nat} {finish' : Complexity.Language.State Γ} {control' : Control result}
      {execution' : RealizedExec program w' depth' stmt entry finish' control'} {steps' : Nat},
      ExecutionCost execution' steps' → steps = steps' := by
  induction first with
  | skip =>
      intro w' depth' finish' control' execution' steps' second
      cases second
      rfl
  | assign =>
      intro w' depth' finish' control' execution' steps' second
      cases second
      rfl
  | letPrim tail ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | letPrim tail' => rw [ih tail']
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits body steps tail ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | @read _ _ _ _ _ _ _ _ _ _ value' _ _ loaded' _ _ _ tail' =>
          have same : value = value' := Except.ok.inj (loaded.symm.trans loaded')
          subst value'
          rw [ih tail']
  | write =>
      intro w' depth' finish' control' execution' steps' second
      cases second
      rfl
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits body steps tail ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | @slice _ _ _ _ _ _ _ _ _ _ _ view' _ _ _ sliced' _ _ _ tail' =>
          have same : view = view' := Except.ok.inj (sliced.symm.trans sliced')
          subst view'
          rw [ih tail']
  | seqNormal firstCost secondCost ihFirst ihSecond =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | seqNormal firstCost' secondCost' =>
          obtain ⟨rfl, _⟩ := observations_eq firstCost firstCost'
          rw [ihFirst firstCost', ihSecond secondCost']
      | seqReturn cost' => cases (observations_eq firstCost cost').2
  | seqReturn cost ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | seqNormal firstCost' secondCost' => cases (observations_eq cost firstCost').2
      | seqReturn cost' => rw [ih cost']
  | iteTrue cost ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | iteTrue cost' => rw [ih cost']
      | iteFalse cost' => simp_all
  | iteFalse cost ih =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | iteTrue cost' => simp_all
      | iteFalse cost' => rw [ih cost']
  | whileFalse guardCost ihGuard =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | whileFalse guardCost' => rw [ihGuard guardCost']
      | whileTrue guardCost' bodyCost' restCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileReturn guardCost' bodyCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
  | whileTrue guardCost bodyCost restCost ihGuard ihBody ihRest =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | whileFalse guardCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileTrue guardCost' bodyCost' restCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          obtain ⟨rfl, _⟩ := observations_eq bodyCost bodyCost'
          rw [ihGuard guardCost', ihBody bodyCost', ihRest restCost']
      | whileReturn guardCost' bodyCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          cases (observations_eq bodyCost bodyCost').2
  | whileReturn guardCost bodyCost ihGuard ihBody =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | whileFalse guardCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileTrue guardCost' bodyCost' restCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          cases (observations_eq bodyCost bodyCost').2
      | whileReturn guardCost' bodyCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          rw [ihGuard guardCost', ihBody bodyCost']
  | ret =>
      intro w' depth' finish' control' execution' steps' second
      cases second
      rfl
  | callReturn calleeCost bodyCost ihCallee ihBody =>
      intro w' depth' finish' control' execution' steps' second
      cases second with
      | callReturn calleeCost' bodyCost' =>
          obtain ⟨rfl, sameControl⟩ := observations_eq calleeCost calleeCost'
          cases Control.returned.inj sameControl
          rw [ihCallee calleeCost', ihBody bodyCost']

end ExecutionCost

end Ram.LanguageCompiler
