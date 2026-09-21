/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Models
import Complexity.Language.Eval.Locals.Range.LocalReturn

/-!
# Arena cost bounds for locally completing ranges

A saved local result finishes the actual body normally, then leaves through the
masked false guard. The represented mathematical phase distinguishes this path
from a continuing round without adding a source variable or another loop.
The completed guard retains its own cost certificate at the actual final heap.

This rule reuses `StmtArenaCostBound.while_model`. It neither proves termination
again nor replaces a local result by an enclosing function return. Positive
stride, word ranges and sufficient capacity are not needed to bound an already
supplied ready execution.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language
open scoped Part.TotalCorrectness

/-- Bound the same local-completion range using its heap-indexed single-round
observations. Continuing rounds preserve the mathematical invariant. Completing
rounds retain the cursor and pay for the stopped guard as well as the normal
round and false-exit overheads, namely `10 + 11`. No invariant on the completed
mathematical state is imposed, but its state and saved-result representations
remain available to the completed guard's cost certificate. -/
theorem while_range_completion_rel
    {signatures : List Signature} {Γ : List Ty} {result τ : Ty}
    {Mutable Locals α : Type} {w heapLimit depth : Nat}
    (view : Env Γ ≃ Locals) (program : Complexity.Language.Program signatures)
    (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result)
    (pending : Atom Γ (.option τ))
    (stoppedGuard : ∀ state value, pending.eval state.locals = some value →
      Complexity.Language.Exec program guard state state (.returned false))
    (stop stride : Nat) (stateRel : Nat → Mutable → Locals → Heap → Prop)
    (resultRep : Representation α τ)
    (step : Nat → Mutable → Option α × Mutable)
    (guardRel : ∀ index mutable locals heap, stateRel index mutable locals heap →
      pending.eval (view.symm locals) = none →
      ∃ after finish,
        Complexity.Language.Stmt.observe view guard program locals heap =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index mutable after finish ∧ pending.eval (view.symm after) = none)
    (bodyRel : ∀ index mutable locals heap, index < stop →
      stateRel index mutable locals heap → pending.eval (view.symm locals) = none →
      ∃ after finish,
        Complexity.Language.Stmt.observe view body program locals heap =
          Part.some ((.normal, after), finish) ∧
        stateRel (if (step index mutable).1.isSome then index else index + stride)
          (step index mutable).2 after finish ∧
        resultRep.option.Rel (step index mutable).1 (pending.eval (view.symm after)) finish)
    (invariant : Nat → Mutable → Prop)
    (guardBound bodyBound potential : Nat → Mutable → Nat)
    (completedGuardBound : Nat → Mutable → α → Nat)
    (guardCost : ∀ index mutable locals heap, invariant index mutable →
      stateRel index mutable locals heap → pending.eval (view.symm locals) = none →
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩
        (guardBound index mutable))
    (bodyCost : ∀ index mutable locals heap, invariant index mutable → index < stop →
      stateRel index mutable locals heap → pending.eval (view.symm locals) = none →
      StmtArenaCostBound program w heapLimit depth body ⟨view.symm locals, heap⟩
        (bodyBound index mutable))
    (completedGuardCost : ∀ index mutable value locals heap,
      stateRel index mutable locals heap →
      resultRep.option.Rel (some value) (pending.eval (view.symm locals)) heap →
      StmtArenaCostBound program w heapLimit depth guard ⟨view.symm locals, heap⟩
        (completedGuardBound index mutable value))
    (falseExit : ∀ index mutable, invariant index mutable → ¬ index < stop →
      guardBound index mutable + 11 ≤ potential index mutable)
    (normalStep : ∀ index mutable, invariant index mutable → index < stop →
      (step index mutable).1 = none →
      invariant (index + stride) (step index mutable).2 ∧
        guardBound index mutable + bodyBound index mutable +
          potential (index + stride) (step index mutable).2 + 10 ≤ potential index mutable)
    (completedStep : ∀ index mutable value, invariant index mutable → index < stop →
      (step index mutable).1 = some value →
      guardBound index mutable + bodyBound index mutable +
        completedGuardBound index (step index mutable).2 value + 21 ≤ potential index mutable)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (represented : stateRel start mutable locals heap)
    (running : pending.eval (view.symm locals) = none) (initial : invariant start mutable) :
    StmtArenaCostBound program w heapLimit depth (.while guard body)
      ⟨view.symm locals, heap⟩ (potential start mutable) := by
  let modelRel (model : Option α × Nat × Mutable) (locals : Locals) (heap : Heap) : Prop :=
    stateRel model.2.1 model.2.2 locals heap ∧
      resultRep.option.Rel model.1 (pending.eval (view.symm locals)) heap
  let test (model : Option α × Nat × Mutable) : Bool :=
    model.1.elim (decide (model.2.1 < stop)) (fun _ => false)
  let advance (model : Option α × Nat × Mutable) : Option α × Nat × Mutable :=
    ((step model.2.1 model.2.2).1,
      (if (step model.2.1 model.2.2).1.isSome then model.2.1 else model.2.1 + stride),
      (step model.2.1 model.2.2).2)
  let valid (model : Option α × Nat × Mutable) : Prop :=
    model.1.elim (invariant model.2.1 model.2.2) (fun _ => True)
  let guardBudget (model : Option α × Nat × Mutable) : Nat :=
    model.1.elim (guardBound model.2.1 model.2.2)
      (completedGuardBound model.2.1 model.2.2)
  let bodyBudget (model : Option α × Nat × Mutable) : Nat :=
    model.1.elim (bodyBound model.2.1 model.2.2) (fun _ => 0)
  let budget (model : Option α × Nat × Mutable) : Nat :=
    model.1.elim (potential model.2.1 model.2.2)
      (fun value => completedGuardBound model.2.1 model.2.2 value + 11)
  have pending_none {locals : Locals} {heap : Heap}
      (saved : resultRep.option.Rel none (pending.eval (view.symm locals)) heap) :
      pending.eval (view.symm locals) = none := by
    cases stored : pending.eval (view.symm locals) with
    | none => rfl
    | some value => simp only [Representation.option, stored] at saved
  have guardSpec : ∀ model,
      Complexity.Language.Stmt.BlockSpec
        (fun locals => Complexity.Language.Stmt.observe view guard program locals) (modelRel model)
        (fun _ _ _ _ => False)
        (fun _ _ again output finish => again = test model ∧ modelRel model output finish) := by
    rintro ⟨phase, index, current⟩ entry entryHeap ⟨related, saved⟩
    cases phase with
    | none =>
        obtain ⟨after, finish, executed, retained, empty⟩ :=
          guardRel index current entry entryHeap related (pending_none saved)
        apply Part.TotalCorrectness.stateT_triple_of_eq executed
        exact ⟨rfl, retained, by simp only [empty, Representation.option]⟩
    | some value =>
        cases stored : pending.eval (view.symm entry) with
        | none => simp only [Representation.option, stored] at saved
        | some actual =>
            have executed : Complexity.Language.Stmt.observe view guard program entry entryHeap =
                Part.some ((.returned false, entry), entryHeap) :=
              Complexity.Language.Stmt.observe_eq_some_iff.mpr
                (stoppedGuard ⟨view.symm entry, entryHeap⟩ actual stored)
            apply Part.TotalCorrectness.stateT_triple_of_eq executed
            exact ⟨rfl, related, saved⟩
  have bodySpec : ∀ model, test model = true →
      Complexity.Language.Stmt.BlockSpec
        (fun locals => Complexity.Language.Stmt.observe view body program locals) (modelRel model)
        (fun _ _ output finish => modelRel (advance model) output finish)
        (fun _ _ _ _ _ => False) := by
    rintro ⟨phase, index, current⟩ active entry entryHeap ⟨related, saved⟩
    cases phase with
    | none =>
        have inside : index < stop := by
          simpa only [test, Option.elim_none, decide_eq_true_eq] using active
        obtain ⟨after, finish, executed, retained, completed⟩ :=
          bodyRel index current entry entryHeap inside related (pending_none saved)
        apply Part.TotalCorrectness.stateT_triple_of_eq executed
        exact ⟨retained, completed⟩
    | some value => simp only [test, Option.elim_some, Bool.false_eq_true] at active
  refine @while_model _ _ _ _ _ view program guard body modelRel test advance guardSpec bodySpec
    valid ?_ w heapLimit depth guardBudget bodyBudget budget ?_ ?_ ?_ ?_
    (none, start, mutable) locals heap
    initial ⟨represented, ?_⟩
  · rintro ⟨phase, index, current⟩ currentValid active
    cases phase with
    | none =>
        have inside : index < stop := by
          simpa only [test, Option.elim_none, decide_eq_true_eq] using active
        cases completed : (step index current).1 with
        | none =>
            simpa only [valid, advance, completed, Option.elim_none, Option.isSome_none,
              Bool.false_eq_true, if_false] using
              (normalStep index current currentValid inside completed).1
        | some value => simp only [valid, advance, completed, Option.elim_some]
    | some value => simp only [test, Option.elim_some, Bool.false_eq_true] at active
  · rintro ⟨phase, index, current⟩ entry entryHeap currentValid ⟨related, saved⟩
    cases phase with
    | none => exact @guardCost index current entry entryHeap currentValid related (pending_none saved)
    | some value => exact @completedGuardCost index current value entry entryHeap related saved
  · rintro ⟨phase, index, current⟩ entry entryHeap currentValid active ⟨related, saved⟩
    cases phase with
    | none =>
        have inside : index < stop := by
          simpa only [test, Option.elim_none, decide_eq_true_eq] using active
        exact @bodyCost index current entry entryHeap currentValid inside related (pending_none saved)
    | some value => simp only [test, Option.elim_some, Bool.false_eq_true] at active
  · rintro ⟨phase, index, current⟩ currentValid stopped
    cases phase with
    | none =>
        exact falseExit index current currentValid
          (by simpa only [test, Option.elim_none, decide_eq_false_iff_not] using stopped)
    | some value => exact Nat.le_refl _
  · rintro ⟨phase, index, current⟩ currentValid active
    cases phase with
    | none =>
        have inside : index < stop := by
          simpa only [test, Option.elim_none, decide_eq_true_eq] using active
        cases completed : (step index current).1 with
        | none =>
            simpa only [guardBudget, bodyBudget, budget, advance, completed, Option.elim_none,
              Option.isSome_none, Bool.false_eq_true, if_false] using
              (normalStep index current currentValid inside completed).2
        | some value =>
            have paid := completedStep index current value currentValid inside completed
            simp only [guardBudget, bodyBudget, budget, advance, completed,
              Option.elim_none, Option.elim_some, Option.isSome_some, if_true]
            omega
    | some value => simp only [test, Option.elim_some, Bool.false_eq_true] at active
  · simp only [running, Representation.option]

end Ram.LanguageCompiler.StmtArenaCostBound
