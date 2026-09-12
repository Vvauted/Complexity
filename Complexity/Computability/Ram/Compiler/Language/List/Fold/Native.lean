/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Native
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Resources
import Complexity.Computability.Ram.Compiler.Language.List.Fold.Asymptotics
import Complexity.Computability.Ram.Compiler.Language.List.Fold.ReadOnly
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.ReadOnly

/-!
# Ordinary-parameter contracts for a compiled read-only fold

The caller supplies ordinary accumulator/root predicates and mathematical
representation, domain and range facts. This connection layer constructs the
argument environment and resource index, eliminates zero-growth capacity work,
and reuses the existing source, arena and fixed-placement contracts for the same
fold entry. It neither unfolds the traversal nor chooses a decoder for a shared
or partially represented accumulator.

`realizable_of_resources` accepts any heap-indexed accumulator representation,
with the existing read-only condition on the callback program and no time-bound
premise. `realizable` retains its compatible signature. `costBound` is conditional
on an existing realized execution and does not need that effect condition.
Both use zero-growth callback contracts at a numeric arena limit of zero only
for proof transport; no source heap or actual RAM placement is replaced.
The supplied bounds retain the existing body-initialization convention.

The source layer's `List.Fold.total_of_eval_eq` separately transports an ordinary
action equation to a source contract, without a resource premise. The ordinary
list and accumulator mathematics, including algorithm-specific range arguments,
remain with the caller.
-/

namespace Ram.LanguageCompiler.List.Fold.Native

open Complexity.Language
open Complexity.Language.List.Fold (onArgs)

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

private theorem resource_input
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop} {w : Nat}
    (positive : 0 < w) (mathematical : α) (values : _root_.List (CellValue kind))
    (actual : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    (related : representation.Rel mathematical actual heap)
    (observed : NodeRef.Contents heap root values)
    (allowed : Complexity.Language.List.Fold.Admissible step domain mathematical values)
    (accFits : ValueFits w actual)
    (headFits : ∀ head ∈ values, ValueFits w (kind.toValue head)) :
    functionPre representation step domain w 0 (fun _ _ => 0)
        (mathematical, values, actual, root) heap ∧
      EnvFits w (foldArgs actual root) ∧
      accumulated step (fun _ _ => 0) mathematical values ≤ 0 := by
  refine ⟨⟨allowed, related, observed, accFits, headFits, ?_⟩, ?_, ?_⟩
  · simp only [accumulated_const, Nat.mul_zero, Nat.le_refl]
  · exact EnvFits.cons (τ := accTy)
      (EnvFits.cons (τ := .option (.node kind)) (EnvFits.empty w)
        root (ValueFits.option_node positive root)) actual accFits
  · simp only [accumulated_const, Nat.mul_zero, Nat.le_refl]

/-- Reuse a zero-growth callback's proved resources for the actual read-only
fold entry. The author's premise contains only ordinary arguments, mathematical
contents/representation, callback admissibility and value ranges. -/
theorem realizable_of_resources
    {source : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract source fn same representation step domain)
    {w depth : Nat}
    (resources : CalleeResources source fn same representation domain w 0 depth (fun _ _ => 0))
    (readOnly : ∀ index, NoHeapWrites (source.body index))
    (positive : 0 < w)
    {pre : Value accTy → Option (NodeRef kind) → Heap → Prop}
    (input : ∀ actual root heap, pre actual root heap →
      ∃ mathematical values,
        representation.Rel mathematical actual heap ∧ NodeRef.Contents heap root values ∧
        Complexity.Language.List.Fold.Admissible step domain mathematical values ∧
        ValueFits w actual ∧ (∀ head ∈ values, ValueFits w (kind.toValue head))) :
    FunctionRealizable (Complexity.Language.List.Fold.program source fn same) w (depth + 1)
      (Complexity.Language.List.Fold.entry accTy kind signatures) (onArgs pre) := by
  refine FunctionRealizable.of_arenaResources (post := fun _ _ _ _ => True)
    (functionResources_of_ready correct resources positive) ?_
    (program_noHeapWrites source fn same readOnly) ?_
  · intro args heap admitted
    obtain ⟨mathematical, values, related, observed, allowed, _, _⟩ :=
      input args.head args.tail.head heap admitted
    obtain ⟨finish, value, execution, _⟩ :=
      Complexity.Language.List.Fold.program_total correct mathematical values allowed
        args heap ⟨related, observed⟩
    exact ⟨finish, value, execution, trivial⟩
  · refine (Env.forall_cons (τ := accTy) (Γ := [.option (.node kind)]) _).mpr ?_
    intro actual
    refine (Env.forall_cons (τ := .option (.node kind)) (Γ := []) _).mpr ?_
    intro root
    refine (Env.forall_nil _).mpr ?_
    intro heap admitted
    obtain ⟨mathematical, values, related, observed, allowed, accFits, headFits⟩ :=
      input actual root heap admitted
    have ready := resource_input positive mathematical values actual root heap
      related observed allowed accFits headFits
    exact ⟨(mathematical, values, actual, root), rfl, ready⟩

set_option linter.unusedVariables false in
/-- Compatibility entry point retaining the supplied callback time bound.
Readiness itself uses only the callback's resource certificate. -/
theorem realizable
    {source : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract source fn same representation step domain)
    {w depth : Nat} {bound : α → CellValue kind → Nat}
    (resources : CalleeResources source fn same representation domain w 0 depth (fun _ _ => 0))
    (bounded : CalleeCostBound source fn same representation domain w 0 depth bound)
    (readOnly : ∀ index, NoHeapWrites (source.body index))
    (positive : 0 < w)
    {pre : Value accTy → Option (NodeRef kind) → Heap → Prop}
    (input : ∀ actual root heap, pre actual root heap →
      ∃ mathematical values,
        representation.Rel mathematical actual heap ∧ NodeRef.Contents heap root values ∧
        Complexity.Language.List.Fold.Admissible step domain mathematical values ∧
        ValueFits w actual ∧ (∀ head ∈ values, ValueFits w (kind.toValue head))) :
    FunctionRealizable (Complexity.Language.List.Fold.program source fn same) w (depth + 1)
      (Complexity.Language.List.Fold.entry accTy kind signatures) (onArgs pre) := by
  clear bounded
  exact realizable_of_resources correct resources readOnly positive input

/-- Transfer the same fold body's count to a bound in ordinary source
parameters. Mathematical witnesses may depend on the actual heap; no inverse
of their representation is assumed or executed. -/
theorem costBound
    {source : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind}
    {representation : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Complexity.Language.List.Fold.Contract source fn same representation step domain)
    {w depth : Nat} {bound : α → CellValue kind → Nat}
    (resources : CalleeResources source fn same representation domain w 0 depth (fun _ _ => 0))
    (bounded : CalleeCostBound source fn same representation domain w 0 depth bound)
    (positive : 0 < w)
    {pre : Value accTy → Option (NodeRef kind) → Heap → Prop}
    {budget : Value accTy → Option (NodeRef kind) → Heap → Nat}
    (input : ∀ actual root heap, pre actual root heap →
      ∃ mathematical values,
        representation.Rel mathematical actual heap ∧ NodeRef.Contents heap root values ∧
        Complexity.Language.List.Fold.Admissible step domain mathematical values ∧
        ValueFits w actual ∧ (∀ head ∈ values, ValueFits w (kind.toValue head)) ∧
        functionBound source fn same step bound mathematical values ≤ budget actual root heap) :
    FunctionCostBound (Complexity.Language.List.Fold.program source fn same)
      (Complexity.Language.List.Fold.entry accTy kind signatures) (onArgs pre) (onArgs budget) := by
  apply FunctionCostBound.of_arenaCostBound
    (functionResources_of_ready correct resources positive)
    (functionCostBound correct resources bounded positive)
  refine (Env.forall_cons (τ := accTy) (Γ := [.option (.node kind)]) _).mpr ?_
  intro actual
  refine (Env.forall_cons (τ := .option (.node kind)) (Γ := []) _).mpr ?_
  intro root
  refine (Env.forall_nil _).mpr ?_
  intro heap admitted
  obtain ⟨mathematical, values, related, observed, allowed, accFits, headFits, boundedInput⟩ :=
    input actual root heap admitted
  obtain ⟨admissible, fits, capacity⟩ := resource_input positive mathematical values actual root heap
    related observed allowed accFits headFits
  exact ⟨(mathematical, values, actual, root), rfl, admissible, fits, capacity, boundedInput⟩

end Ram.LanguageCompiler.List.Fold.Native
