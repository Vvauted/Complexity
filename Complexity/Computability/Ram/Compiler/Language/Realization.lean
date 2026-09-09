/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Layout
import Complexity.Language.Eval.Verification

/-!
# Source-level realization conditions for the word backend

`RealizedExec` retains the same successful finite source execution while recording
the mathematical scalar ranges and sufficient maximum call nesting used by the
word backend. Its depth parameter is a nesting capacity, not an instruction
budget: a call's continuation and sequential siblings reuse the caller's depth.

Erasure gives the independent `Complexity.Language.Exec`. No target execution,
register assignment or chosen instruction count occurs in these conditions.
The current source fragment has immutable scalar locals and no heap operations.
It nevertheless threads the actual shared heap through each scope and call;
caller-local restoration never resets the callee's final heap.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A successful source execution whose actual operations fit the selected word
width and whose nested calls fit a given capacity. -/
inductive RealizedExec {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w : Nat) :
    Nat → {Γ : List Ty} → {result : Ty} → Complexity.Language.Stmt signatures Γ result →
      Complexity.Language.State Γ → Complexity.Language.State Γ → Control result → Prop where
  | skip {Γ : List Ty} {result : Ty} {depth : Nat} (entry : Complexity.Language.State Γ) :
      RealizedExec program w depth
        (.skip : Complexity.Language.Stmt signatures Γ result) entry entry .normal
  | letPrim {Γ : List Ty} {τ result : Ty} {depth : Nat} {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
      {control : Control result}
      (fits : PrimFits w entry.locals value)
      (body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (value.eval entry.locals) entry) finish control) :
      RealizedExec program w depth (.letPrim value continuation) entry finish.tail control
  | seqNormal {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Complexity.Language.State Γ} {control : Control result}
      (head : RealizedExec program w depth first entry middle .normal)
      (tail : RealizedExec program w depth second middle finish control) :
      RealizedExec program w depth (.seq first second) entry finish control
  | seqReturn {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {value : Value result}
      (head : RealizedExec program w depth first entry finish (.returned value)) :
      RealizedExec program w depth (.seq first second) entry finish (.returned value)
  | iteTrue {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (test : condition.eval entry.locals = true)
      (body : RealizedExec program w depth yes entry finish control) :
      RealizedExec program w depth (.ite condition yes no) entry finish control
  | iteFalse {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (test : condition.eval entry.locals = false)
      (body : RealizedExec program w depth no entry finish control) :
      RealizedExec program w depth (.ite condition yes no) entry finish control
  | ret {Γ : List Ty} {result : Ty} {depth : Nat}
      (value : Atom Γ result) (entry : Complexity.Language.State Γ)
      (fits : valueToNat (value.eval entry.locals) < 2 ^ w) :
      RealizedExec program w depth (.ret value) entry entry (.returned (value.eval entry.locals))
  | callReturn {Γ : List Ty} {result : Ty} {depth : Nat} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {calleeFinish : Complexity.Language.State signatures[fn].params}
      {value : Value signatures[fn].result}
      {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
      {control : Control result}
      (arguments : EnvFits w (args.eval entry.locals))
      (callee : RealizedExec program w depth (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value))
      (body : RealizedExec program w (depth + 1) continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control) :
      RealizedExec program w (depth + 1) (.call fn args continuation) entry finish.tail control

/-- A successful control outcome carries either no value or a representable
returned value. This predicate depends on the outcome, never its execution proof. -/
def ControlFits (w : Nat) {result : Ty} (control : Control result) : Prop :=
  match control with
  | .normal => True
  | .returned value => valueToNat value < 2 ^ w
  | .fault _ => False

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {control : Control result}

/-- Realization certifies the same independent source execution. -/
theorem erase (execution : RealizedExec program w depth stmt entry finish control) :
    Complexity.Language.Exec program stmt entry finish control := by
  induction execution with
  | skip entry => exact .skip entry
  | letPrim fits body ih => exact .letPrim ih
  | seqNormal head tail ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn head ih => exact .seqReturn ih
  | iteTrue test body ih => exact .iteTrue test ih
  | iteFalse test body ih => exact .iteFalse test ih
  | ret value entry fits => exact .ret value entry
  | callReturn arguments callee body ihCallee ihBody => exact .callReturn ihCallee ihBody

/-- This immutable scalar fragment preserves the enclosing lexical environment.
New inner bindings are discarded on scope exit, including when returning. -/
theorem locals_eq (execution : RealizedExec program w depth stmt entry finish control) :
    finish.locals = entry.locals := execution.erase.locals_eq

/-- The current scalar statement vocabulary has no heap operations. This follows
from its execution rules, not from caller restoration or a heap representation. -/
theorem heap_eq (execution : RealizedExec program w depth stmt entry finish control) :
    finish.heap = entry.heap := execution.erase.heap_eq

/-- Every actual returned scalar is representable; successful normal continuation
requires no result value, and a realized execution cannot fault. -/
theorem outcome_fits (execution : RealizedExec program w depth stmt entry finish control) :
    ControlFits w control := by
  induction execution with
  | skip => trivial
  | letPrim fits body ih => exact ih
  | seqNormal head tail ihHead ihTail => exact ihTail
  | seqReturn head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | ret value entry fits => exact fits
  | callReturn arguments callee body ihCallee ihBody => exact ihBody

/-- A caller may use the actual returned value's word range. -/
theorem returned_fits {value : Value result}
    (execution : RealizedExec program w depth stmt entry finish (.returned value)) :
    valueToNat value < 2 ^ w := execution.outcome_fits

/-- More allowed call nesting preserves the same execution and values. This
does not add instructions or change the word-range conditions. -/
theorem mono_depth (execution : RealizedExec program w depth stmt entry finish control)
    {depth' : Nat} (capacity : depth ≤ depth') :
    RealizedExec program w depth' stmt entry finish control := by
  induction execution generalizing depth' with
  | skip entry => exact .skip entry
  | letPrim fits body ih => exact .letPrim fits (ih capacity)
  | seqNormal head tail ihHead ihTail => exact .seqNormal (ihHead capacity) (ihTail capacity)
  | seqReturn head ih => exact .seqReturn (ih capacity)
  | iteTrue test body ih => exact .iteTrue test (ih capacity)
  | iteFalse test body ih => exact .iteFalse test (ih capacity)
  | ret value entry fits => exact .ret value entry fits
  | callReturn arguments callee body ihCallee ihBody =>
      cases depth' with
      | zero => omega
      | succ depth' =>
          exact .callReturn arguments
            (ihCallee (Nat.le_of_succ_le_succ capacity)) (ihBody capacity)

end RealizedExec

/-- Structural realization conditions with the source language's two successful
postconditions. The extra parameter records call capacity, not elapsed time. -/
def RealizationWP {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Complexity.Language.Program signatures) (w depth : Nat)
    (stmt : Complexity.Language.Stmt signatures Γ result)
    (normal : Complexity.Language.State Γ → Prop)
    (returned : Value result → Complexity.Language.State Γ → Prop)
    (entry : Complexity.Language.State Γ) : Prop :=
  ∃ finish control, RealizedExec program w depth stmt entry finish control ∧
    control.Satisfies normal returned finish

namespace RealizationWP

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Complexity.Language.Program signatures} {w depth : Nat}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {normal normal' : Complexity.Language.State Γ → Prop}
variable {returned returned' : Value result → Complexity.Language.State Γ → Prop}
variable {entry : Complexity.Language.State Γ}

/-- Erasing ranges and nesting gives total correctness of the same source node. -/
theorem erase (h : RealizationWP program w depth stmt normal returned entry) :
    Complexity.Language.TotalWP program stmt normal returned entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  exact ⟨finish, control, execution.erase, post⟩

/-- Weaken ordinary source postconditions while retaining realization. -/
theorem mono_post (h : RealizationWP program w depth stmt normal returned entry)
    (hnormal : ∀ finish, normal finish → normal' finish)
    (hreturned : ∀ value finish, returned value finish → returned' value finish) :
    RealizationWP program w depth stmt normal' returned' entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  refine ⟨finish, control, execution, ?_⟩
  cases control with
  | normal => exact hnormal finish post
  | returned value => exact hreturned value finish post
  | fault fault => exact post

/-- Increase the available nesting without changing source postconditions. -/
theorem mono_depth (h : RealizationWP program w depth stmt normal returned entry)
    {depth' : Nat} (capacity : depth ≤ depth') :
    RealizationWP program w depth' stmt normal returned entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  exact ⟨finish, control, execution.mono_depth capacity, post⟩

@[simp] theorem skip_iff :
    RealizationWP program w depth .skip normal returned entry ↔ normal entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .normal, .skip entry, post⟩

/-- Return materialization requires the actual source result to fit. -/
@[simp] theorem ret_iff (value : Atom Γ result) :
    RealizationWP program w depth (.ret value) normal returned entry ↔
      valueToNat (value.eval entry.locals) < 2 ^ w ∧ returned (value.eval entry.locals) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | ret value entry fits => exact ⟨fits, post⟩
  · rintro ⟨fits, post⟩
    exact ⟨entry, .returned (value.eval entry.locals), .ret value entry fits, post⟩

/-- The primitive's range and the scoped continuation concern its actual value. -/
@[simp] theorem letPrim_iff {τ : Ty} (value : Prim Γ τ)
    (continuation : Complexity.Language.Stmt signatures (τ :: Γ) result) :
    RealizationWP program w depth (.letPrim value continuation) normal returned entry ↔
      PrimFits w entry.locals value ∧
        RealizationWP program w depth continuation (fun finish => normal finish.tail)
          (fun value finish => returned value finish.tail)
          (Complexity.Language.State.cons (value.eval entry.locals) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | letPrim fits body => exact ⟨fits, _, control, body, post⟩
  · rintro ⟨fits, finish, control, execution, post⟩
    exact ⟨finish.tail, control, .letPrim fits execution, post⟩

/-- Sequential siblings reuse the same nesting capacity; returns skip the tail. -/
@[simp] theorem seq_iff (first second : Complexity.Language.Stmt signatures Γ result) :
    RealizationWP program w depth (.seq first second) normal returned entry ↔
      RealizationWP program w depth first
        (RealizationWP program w depth second normal returned) returned entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | seqNormal firstExec secondExec =>
        exact ⟨_, .normal, firstExec, finish, control, secondExec, post⟩
    | seqReturn firstExec => exact ⟨_, _, firstExec, post⟩
  · rintro ⟨middle, control, execution, post⟩
    cases control with
    | normal =>
        obtain ⟨finish, control, next, post⟩ := post
        exact ⟨finish, control, .seqNormal execution next, post⟩
    | returned value => exact ⟨middle, .returned value, .seqReturn execution, post⟩
    | fault fault => exact False.elim post

/-- Only the selected source branch must satisfy operation ranges. -/
@[simp] theorem ite_iff (condition : Atom Γ .bool)
    (yes no : Complexity.Language.Stmt signatures Γ result) :
    RealizationWP program w depth (.ite condition yes no) normal returned entry ↔
      if condition.eval entry.locals then RealizationWP program w depth yes normal returned entry
      else RealizationWP program w depth no normal returned entry := by
  cases hcondition : condition.eval entry.locals with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => cases hcondition.symm.trans truth
        | iteFalse truth body => exact ⟨finish, control, body, post⟩
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteFalse hcondition execution, post⟩
  | true =>
      simp only [↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => exact ⟨finish, control, body, post⟩
        | iteFalse truth body => cases hcondition.symm.trans truth
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteTrue hcondition execution, post⟩

end RealizationWP

/-- A function's source-level admissibility conditions suffice for its actual
successful execution with the selected scalar ranges and call capacity. The
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
      valueToNat value < 2 ^ w →
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
    (body : valueToNat value < 2 ^ w →
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
