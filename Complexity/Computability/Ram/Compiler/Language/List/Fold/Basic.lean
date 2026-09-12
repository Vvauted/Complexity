/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Program
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources
import Complexity.Computability.Ram.Compiler.Language.MeasuredNode
import Complexity.Computability.Ram.Compiler.Language.Validity

/-!
# Shared arguments and bounds for linked-list folding

Callback domains, actual source arguments and accumulated envelopes are shared
by readiness and cost proofs. These definitions do not choose a traversal or
require a proposed instruction bound to establish successful execution.
The guard's measured primitive proof retains its existing branch counts.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

universe u

variable {α : Type u} {accTy : Ty} {kind : CellTy} {signatures : _root_.List Signature}

/-- Mathematical charge accumulated along the ordinary fold trajectory.
This is an envelope on supplied bounds, not a source execution or cost model. -/
def accumulated (step : α → CellValue kind → α) (charge : α → CellValue kind → Nat) :
    α → _root_.List (CellValue kind) → Nat
  | _, [] => 0
  | accumulator, head :: tail =>
      charge accumulator head + accumulated step charge (step accumulator head) tail

/-- A fixed per-element overhead separates from the accumulator-dependent
callback charges without changing which accumulator supplies each bound. -/
theorem accumulated_add_const (step : α → CellValue kind → α)
    (charge : α → CellValue kind → Nat) (overhead : Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) :
    accumulated step (fun a head => charge a head + overhead) accumulator values =
      accumulated step charge accumulator values + values.length * overhead := by
  induction values generalizing accumulator with
  | nil => simp only [accumulated, _root_.List.length_nil, Nat.zero_mul, Nat.add_zero]
  | cons head tail ih =>
      simp only [accumulated, _root_.List.length_cons, ih, Nat.add_mul, Nat.one_mul]
      omega

/-- Each index keeps the mathematical accumulator and its actual source value;
heap representations need not choose a unique runtime encoding. -/
def calleeArgs (input : α × Value accTy × CellValue kind) : Env [accTy, kind.toTy] :=
  Env.cons (τ := accTy) input.2.1
    (Env.cons (τ := kind.toTy) (kind.toValue input.2.2) Env.empty)

/-- The callback domain and accumulator observation are checked at the actual
entry heap, rather than turning the representation into a host-side decoder. -/
def calleePre (representation : Representation α accTy)
    (domain : α → CellValue kind → Prop)
    (input : α × Value accTy × CellValue kind) (heap : Heap) : Prop :=
  domain input.1 input.2.2 ∧ representation.Rel input.1 input.2.1 heap

/-- Fold specializes the shared resource interface to the selected callback;
the reservation depends on the mathematical accumulator and current head. -/
abbrev CalleeResources (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (representation : Representation α accTy) (domain : α → CellValue kind → Prop)
    (w heapLimit depth : Nat) (reserve : α → CellValue kind → Nat) : Prop :=
  FunctionArenaResources program (Complexity.Language.List.Fold.calleeBody program fn same)
    calleeArgs (calleePre representation domain) w heapLimit depth
    (fun input => reserve input.1 input.2.2)

/-- Callback bounds retain the shared convention: actual core steps plus the
two function-initialization instructions, before the caller adds its frame work. -/
abbrev CalleeCostBound (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (representation : Representation α accTy) (domain : α → CellValue kind → Prop)
    (w heapLimit depth : Nat) (bound : α → CellValue kind → Nat) : Prop :=
  FunctionArenaCostBound program (Complexity.Language.List.Fold.calleeBody program fn same)
    calleeArgs (calleePre representation domain) w heapLimit depth
    (fun input => bound input.1 input.2.2)

/-- The emitted call overhead and one round of actual linked traversal are
added to the callback's independently supplied bound at each accumulator. -/
def remainingCost (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (accTy : Ty)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) : Nat :=
  accumulated step
    (fun a head => callCost program fn (bound a head) + 2 * fieldCount accTy + 45)
    accumulator values

/-- Callback charges along the ordinary fold trajectory separate from the
compiler's linear traversal and actual calling-convention overhead. -/
theorem remainingCost_eq_sum (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) (accTy : Ty)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (accumulator : α) (values : _root_.List (CellValue kind)) :
    remainingCost program fn accTy step bound accumulator values =
      accumulated step bound accumulator values +
        values.length * (callCost program fn 0 + 2 * fieldCount accTy + 45) := by
  have charges :
      (fun a head => callCost program fn (bound a head) + 2 * fieldCount accTy + 45) =
        (fun a head => bound a head +
          (callCost program fn 0 + 2 * fieldCount accTy + 45)) := by
    funext a head
    rw [callCost_eq_add]
    omega
  rw [remainingCost, charges, accumulated_add_const]

/-- Every represented list head already has its scalar range in the actual
initial memory. Later callbacks retain these immutable stored heads. -/
theorem contents_valueFits {w heapLimit : Nat} {placement : Nat → Word w}
    {heap : Heap} {initial : Source.State w} {root : Option (NodeRef kind)}
    {values : _root_.List (CellValue kind)}
    (memory : HeapRep placement heapLimit heap initial)
    (observed : NodeRef.Contents heap root values) :
    ∀ head ∈ values, ValueFits w (kind.toValue head) := by
  induction observed with
  | nil => simp only [_root_.List.not_mem_nil, false_implies, implies_true]
  | @cons ref head tail rest found contents ih =>
      intro value member
      rcases _root_.List.mem_cons.mp member with rfl | member
      · exact (memory.node_valueFits found).1
      · exact ih value member

/-- The actual guard tests only the optional root and preserves both locals
and heap. Its two branches have their existing, distinct emitted counts. -/
theorem guard_measured (program : Complexity.Language.Program signatures)
    (accumulator : Value accTy) (root : Option (NodeRef kind)) (heap : Heap)
    {w heapLimit depth cursor : Nat} (positive : 0 < w) :
    ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.List.Fold.guard accTy kind)
        (Complexity.Language.List.Fold.state accumulator root heap)
        (Complexity.Language.List.Fold.state accumulator root heap) (.returned root.isSome),
      ∃ ready : ArenaReady execution w heapLimit depth cursor cursor,
        ArenaExecutionCost ready (if root.isSome then 9 else 6) := by
  cases root with
  | none =>
      let initial := Complexity.Language.List.Fold.state accumulator (none : Option (NodeRef kind)) heap
      have falseFits : ValueFits w (τ := .bool) false := Nat.two_pow_pos w
      let execution : Complexity.Language.Exec program
          (Complexity.Language.List.Fold.guard accTy kind)
          initial initial (.returned false) :=
        .matchNone rfl (.ret (.bool false) _)
      let returnReady : ArenaReady (Complexity.Language.Exec.ret (program := program)
          (.bool false) initial) w heapLimit depth cursor cursor :=
        .ret (.bool false) initial falseFits
      let ready : ArenaReady execution w heapLimit depth cursor cursor :=
        .matchNone (entry := initial) (value := .var (.there .here))
          (selected := rfl) returnReady
      exact ⟨execution, ready,
        .matchNone (entry := initial) (value := .var (.there .here))
          (selected := rfl) (ready := returnReady)
          (.ret (.bool false) initial (fits := falseFits))⟩
  | some ref =>
      let initial := Complexity.Language.List.Fold.state accumulator (some ref) heap
      let scopedState := Complexity.Language.State.cons (τ := .node kind) ref initial
      have trueFits : ValueFits w (τ := .bool) true :=
        Nat.one_lt_two_pow (Nat.ne_of_gt positive)
      have refFits : ValueFits w (τ := .node kind) ref := trivial
      let execution : Complexity.Language.Exec program
          (Complexity.Language.List.Fold.guard accTy kind)
          initial initial (.returned true) :=
        .matchSome (finish := scopedState) rfl (.ret (.bool true) scopedState)
      let returnReady : ArenaReady (Complexity.Language.Exec.ret (program := program)
          (.bool true) scopedState) w heapLimit depth cursor cursor :=
        .ret (.bool true) scopedState trueFits
      let ready : ArenaReady execution w heapLimit depth cursor cursor :=
        .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
          (selected := rfl) refFits returnReady
      exact ⟨execution, ready,
        .matchSome (entry := initial) (value := .var (.there .here)) (payload := ref)
          (selected := rfl) (payloadFits := refFits) (ready := returnReady)
          (.ret (.bool true) scopedState (fits := trueFits))⟩

/-- The source invocation receives the original represented accumulator and
linked root. These are existing source arguments, not a host-side list loader. -/
def foldArgs (accumulator : Value accTy) (root : Option (NodeRef kind)) :
    Env [accTy, .option (.node kind)] :=
  Env.cons (τ := accTy) accumulator (Env.cons (τ := .option (.node kind)) root Env.empty)

/-- The complete invocation envelope includes the actual relocated callback
frames, source-body initialization, outer invocation and final halt. -/
def invocationBound (sourceProgram : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (step : α → CellValue kind → α) (bound : α → CellValue kind → Nat)
    (mathematical : α) (values : _root_.List (CellValue kind)) : Nat :=
  let folded := Complexity.Language.List.Fold.program sourceProgram fn same
  LocalCompiler.Function.callSteps (programControl folded)
    (lowerFunc folded (Complexity.Language.List.Fold.entry accTy kind signatures))
    (remainingCost folded (Complexity.Language.List.Fold.calleeEntry accTy kind fn)
      accTy step bound mathematical values + 2 * fieldCount accTy + 23) + 1

end Ram.LanguageCompiler.List.Fold
