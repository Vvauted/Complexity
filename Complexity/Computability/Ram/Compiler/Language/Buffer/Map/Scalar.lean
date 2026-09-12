/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Buffer.Map

/-!
# Reusing scalar function proofs in an allocating map

An existing nonallocating source function does not need a second range or cost
proof to become a map callback. Its `FunctionRealizable` witness retains the
arena cursor, and its `FunctionCostBound` transfers through the proved equality
of the two compiler cost observations. The callback's mathematical contract is
separate and must still establish its result and preservation of old contents.
-/

namespace Ram.LanguageCompiler.BufferMap

open Complexity.Language

variable {signatures : List Signature} {inputKind outputKind : CellTy}

/-- A scalar admissibility condition at the selected function's argument type. -/
def scalarPre {fn : Fin signatures.length}
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (admissible : CellValue inputKind → Prop) : Env signatures[fn].params → Heap → Prop :=
  cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm)
    (fun args _ => admissible (inputKind.ofValue args.head))

/-- An ordinary scalar bound at the selected function's argument type. -/
def scalarBound {fn : Fin signatures.length}
    (same : signatures[fn] = Buffer.Map.signature inputKind outputKind)
    (bound : CellValue inputKind → Nat) : Env signatures[fn].params → Heap → Nat :=
  cast (congrArg (fun s => Env s.params → Heap → Nat) same.symm)
    (fun args _ => bound (inputKind.ofValue args.head))

private theorem realizedInvocationOfEq
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {selected : Signature} (same : signatures[fn] = selected)
    {w depth : Nat} {pre : Env selected.params → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre))
    (args : Env selected.params) (heap : Heap) (allowed : pre args heap) :
    ∃ finish value, RealizedExec program w depth
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) ⟨args, heap⟩ finish (.returned value) := by
  cases same
  exact realizable args heap allowed

private theorem boundedInvocationOfEq
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {selected : Signature} (same : signatures[fn] = selected)
    {pre : Env selected.params → Heap → Prop} {bound : Env selected.params → Heap → Nat}
    (bounded : FunctionCostBound program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s => Env s.params → Heap → Nat) same.symm) bound))
    (args : Env selected.params) (heap : Heap) (allowed : pre args heap)
    {w depth : Nat} {finish : Complexity.Language.State selected.params}
    {value : Value selected.result}
    (execution : RealizedExec program w depth
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) ⟨args, heap⟩ finish (.returned value))
    {steps : Nat} (cost : ExecutionCost execution steps) : steps + 2 ≤ bound args heap := by
  cases same
  exact bounded args heap allowed execution cost

/-- A scalar function's existing realization supplies a zero-growth callback
resource proof. Determinism attaches it to the map's actual source invocation. -/
theorem CalleeResources.of_functionRealizable
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {w heapLimit depth : Nat} {admissible : CellValue inputKind → Prop}
    (realizable : FunctionRealizable program w depth fn (scalarPre same admissible)) :
    CalleeResources program fn same w heapLimit depth 0 admissible := by
  intro value heap cursor allowed _ _ finish returned execution
  obtain ⟨otherFinish, otherValue, realized⟩ :=
    realizedInvocationOfEq same realizable (calleeArgs value) heap
      (by simpa only [calleeArgs, Env.head_cons, CellTy.ofValue_toValue] using allowed)
  obtain ⟨rfl, sameControl⟩ := realized.erase.deterministic execution
  cases Control.returned.inj sameControl
  exact ⟨cursor, realized.arenaReady heapLimit cursor, Nat.le_refl _⟩

/-- Reuse the scalar function's independent bound for the very same arena
execution. No callback count is assigned by its mathematical result function. -/
theorem CalleeCostBound.of_functionCostBound
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = Buffer.Map.signature inputKind outputKind}
    {w heapLimit depth : Nat} {admissible : CellValue inputKind → Prop}
    {bound : CellValue inputKind → Nat}
    (realizable : FunctionRealizable program w depth fn (scalarPre same admissible))
    (bounded : FunctionCostBound program fn (scalarPre same admissible)
      (scalarBound same bound)) :
    CalleeCostBound program fn same w heapLimit depth bound admissible := by
  intro value heap allowed finish returned execution cursor finalCursor ready steps cost
  obtain ⟨otherFinish, otherValue, realized⟩ :=
    realizedInvocationOfEq same realizable (calleeArgs value) heap
      (by simpa only [calleeArgs, Env.head_cons, CellTy.ofValue_toValue] using allowed)
  obtain ⟨otherSteps, otherCost⟩ := realized.exists_cost
  have stepEq : steps = otherSteps := cost.deterministic (otherCost.arena heapLimit cursor)
  have stepBound := boundedInvocationOfEq same bounded (calleeArgs value) heap
    (by simpa only [calleeArgs, Env.head_cons, CellTy.ofValue_toValue] using allowed)
    realized otherCost
  simpa only [stepEq, calleeArgs, Env.head_cons, CellTy.ofValue_toValue] using stepBound

end Ram.LanguageCompiler.BufferMap
