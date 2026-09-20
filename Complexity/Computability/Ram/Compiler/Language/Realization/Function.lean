/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization.WP
import Complexity.Language.Eval.Verification

/-!
# Function realization and call composition

`FunctionRealizable` packages successful source invocations with word ranges and
sufficient call nesting. Call rules reuse an independent mathematical contract
or evaluation equation at the actual returned value and final heap. Only the
continuation's range and nesting obligations remain; correctness acquires no
time-budget premise.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A function's source-level admissibility conditions suffice for its actual
successful execution with the selected value ranges and call capacity. The
mathematical behavior remains in the independent source `FunctionTotal`. -/
def FunctionRealizable {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w depth : Nat)
    (fn : Fin signatures.length) (pre : Env signatures[fn].params → Heap → Prop) : Prop :=
  ∀ args heap, pre args heap → ∃ finish value,
    RealizedExec program w depth (program.body fn) ⟨args, heap⟩ finish (.returned value)

namespace FunctionRealizable

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth : Nat} {fn : Fin signatures.length}
variable {pre pre' : Env signatures[fn].params → Heap → Prop}

/-- Structural range proofs must reach a real return, not a missing-return fault. -/
theorem of_wp (body : ∀ args heap, pre args heap →
    RealizationWP program w depth (program.body fn) (fun _ => False)
      (fun _ _ => True) ⟨args, heap⟩) : FunctionRealizable program w depth fn pre := by
  intro args heap hpre
  obtain ⟨finish, control, execution, post⟩ := body args heap hpre
  cases control with
  | normal => exact False.elim post
  | returned value => exact ⟨finish, value, execution⟩
  | fault fault => exact False.elim post

/-- Existing function realizability supplies the same returned source invocation. -/
theorem wp (h : FunctionRealizable program w depth fn pre)
    (args : Env signatures[fn].params) (heap : Heap) (hpre : pre args heap) :
    RealizationWP program w depth (program.body fn) (fun _ => False)
      (fun _ _ => True) ⟨args, heap⟩ := by
  obtain ⟨finish, value, execution⟩ := h args heap hpre
  exact ⟨finish, .returned value, execution, trivial⟩

/-- A stronger admissibility predicate preserves realizability. -/
theorem consequence (h : FunctionRealizable program w depth fn pre)
    (input : ∀ args heap, pre' args heap → pre args heap) :
    FunctionRealizable program w depth fn pre' :=
  fun args heap hpre => h args heap (input args heap hpre)

/-- More permitted nesting preserves the same source implementation. -/
theorem mono_depth (h : FunctionRealizable program w depth fn pre)
    {depth' : Nat} (capacity : depth ≤ depth') :
    FunctionRealizable program w depth' fn pre := by
  intro args heap hpre
  obtain ⟨finish, value, execution⟩ := h args heap hpre
  exact ⟨finish, value, execution.mono_depth capacity⟩

end FunctionRealizable

namespace RealizationWP

/-- Reuse a separately proved mathematical contract at the actual callee return.
Only the subsequent operation ranges and nesting remain to be established;
the algorithm's result property is not reproved during realization. -/
theorem call {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {w depth calleeDepth : Nat}
    {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w calleeDepth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (arguments : EnvFits w (args.eval entry.locals)) (nesting : calleeDepth + 1 ≤ depth)
    (hfeasible : feasible (args.eval entry.locals) entry.heap)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value finalHeap, post (args.eval entry.locals) entry.heap value finalHeap →
      ValueFits w value →
      RealizationWP program w depth continuation (fun finish => normal finish.tail)
        (fun result finish => returned result finish.tail)
        (Complexity.Language.State.cons value ⟨entry.locals, finalHeap⟩)) :
    RealizationWP program w depth (.call fn args continuation) normal returned entry := by
  obtain ⟨calleeFinish, value, invocation⟩ :=
    realizable (args.eval entry.locals) entry.heap hfeasible
  have property := specification.postcondition hpre invocation.erase
  obtain ⟨finish, control, execution, result⟩ :=
    body value calleeFinish.heap property invocation.returned_fits
  cases depth with
  | zero => omega
  | succ depth =>
      exact ⟨finish.tail, control,
        .callReturn arguments
          (invocation.mono_depth (Nat.le_of_succ_le_succ nesting)) execution, result⟩

/-- Reuse an ordinary equation for this callee invocation directly. The existing
call rule transports the proved value; the caller only establishes realization
of its continuation using the actual returned value's range. -/
theorem call_of_eval {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {w depth calleeDepth : Nat}
    {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    {feasible : Env signatures[fn].params → Heap → Prop}
    {value : Value signatures[fn].result} {finalHeap : Heap}
    (realizable : FunctionRealizable program w calleeDepth fn feasible)
    (evaluated : program.eval fn (args.eval entry.locals) entry.heap =
      Part.some (.ok value, finalHeap))
    (arguments : EnvFits w (args.eval entry.locals)) (nesting : calleeDepth + 1 ≤ depth)
    (hfeasible : feasible (args.eval entry.locals) entry.heap)
    (body : ValueFits w value →
      RealizationWP program w depth continuation (fun finish => normal finish.tail)
        (fun result finish => returned result finish.tail)
        (Complexity.Language.State.cons value ⟨entry.locals, finalHeap⟩)) :
    RealizationWP program w depth (.call fn args continuation) normal returned entry := by
  have specification : FunctionTotal program fn
      (fun actual initial => actual = args.eval entry.locals ∧ initial = entry.heap)
      (fun _ _ returned resultHeap => returned = value ∧ resultHeap = finalHeap) := by
    apply FunctionTotal.iff_eval.mpr
    rintro actual initial ⟨rfl, rfl⟩
    exact ⟨value, finalHeap, evaluated, rfl, rfl⟩
  apply call realizable specification arguments nesting hfeasible ⟨rfl, rfl⟩
  rintro actual actualHeap ⟨rfl, rfl⟩ fits
  exact body fits

end RealizationWP

end Ram.LanguageCompiler
