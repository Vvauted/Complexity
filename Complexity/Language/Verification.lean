/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Semantics

/-!
# Total correctness of typed source programs

`TotalWP` describes a finite execution of the independent source language.
Normal continuation and function return have separate postconditions; a fault
satisfies neither. The structural rules follow actual lexical values, callee
returns and branch conditions without mentioning a machine representation or
an instruction budget.

`FunctionTotal` requires the declared body to return a value. Falling through
the body is not successful function termination. Function contracts compose
through the same `Exec.callReturn` rule as the source semantics.
-/

namespace Complexity.Language

/-- Interpret two successful postconditions at a source control outcome.
Faults cannot establish total correctness. -/
def Control.Satisfies {Γ : List Ty} {result : Ty}
    (normal : Env Γ → Prop) (returned : Value result → Env Γ → Prop)
    (control : Control result) (finish : Env Γ) : Prop :=
  match control with
  | .normal => normal finish
  | .returned value => returned value finish
  | .fault _ => False

/-- Budget-free total correctness, retaining both normal and returning control. -/
def TotalWP {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Program signatures) (stmt : Stmt signatures Γ result)
    (normal : Env Γ → Prop) (returned : Value result → Env Γ → Prop)
    (entry : Env Γ) : Prop :=
  ∃ finish control, Exec program stmt entry finish control ∧
    control.Satisfies normal returned finish

namespace TotalWP

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Program signatures} {stmt : Stmt signatures Γ result}
variable {normal normal' : Env Γ → Prop}
variable {returned returned' : Value result → Env Γ → Prop} {entry : Env Γ}

/-- Weaken either successful postcondition without admitting faults. -/
theorem mono_post (h : TotalWP program stmt normal returned entry)
    (hnormal : ∀ finish, normal finish → normal' finish)
    (hreturned : ∀ value finish, returned value finish → returned' value finish) :
    TotalWP program stmt normal' returned' entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  refine ⟨finish, control, execution, ?_⟩
  cases control with
  | normal => exact hnormal finish post
  | returned value => exact hreturned value finish post
  | fault fault => exact post

@[simp] theorem skip_iff :
    TotalWP program .skip normal returned entry ↔ normal entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .normal, .skip entry, post⟩

@[simp] theorem ret_iff (value : Atom Γ result) :
    TotalWP program (.ret value) normal returned entry ↔
      returned (value.eval entry) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .returned (value.eval entry), .ret value entry, post⟩

/-- A primitive's mathematical value is bound for its actual lexical scope. -/
@[simp] theorem letPrim_iff {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) :
    TotalWP program (.letPrim value continuation) normal returned entry ↔
      TotalWP program continuation (fun finish => normal (Env.tail finish))
        (fun value finish => returned value (Env.tail finish))
        (Env.cons (value.eval entry) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | letPrim body => exact ⟨_, control, body, post⟩
  · rintro ⟨finish, control, execution, post⟩
    exact ⟨Env.tail finish, control, .letPrim execution, post⟩

/-- Sequencing runs the tail only after normal continuation. An actual return
passes directly to the enclosing return postcondition. -/
@[simp] theorem seq_iff (first second : Stmt signatures Γ result) :
    TotalWP program (.seq first second) normal returned entry ↔
      TotalWP program first (TotalWP program second normal returned) returned entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | seqNormal firstExec secondExec =>
        exact ⟨_, .normal, firstExec, finish, control, secondExec, post⟩
    | seqReturn firstExec => exact ⟨_, _, firstExec, post⟩
    | seqFault firstExec => exact False.elim post
  · rintro ⟨middle, control, execution, post⟩
    cases control with
    | normal =>
        obtain ⟨finish, control, next, post⟩ := post
        exact ⟨finish, control, .seqNormal execution next, post⟩
    | returned value => exact ⟨middle, .returned value, .seqReturn execution, post⟩
    | fault fault => exact False.elim post

/-- Source branching depends on the actual Boolean value, not a machine guard. -/
@[simp] theorem ite_iff (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result) :
    TotalWP program (.ite condition yes no) normal returned entry ↔
      if condition.eval entry then TotalWP program yes normal returned entry
      else TotalWP program no normal returned entry := by
  cases hcondition : condition.eval entry with
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

/-- Compose a primitive step after identifying its actual source value. -/
theorem letPrim {τ : Ty} {value : Prim Γ τ}
    {continuation : Stmt signatures (τ :: Γ) result}
    (body : TotalWP program continuation (fun finish => normal (Env.tail finish))
      (fun value finish => returned value (Env.tail finish))
      (Env.cons (value.eval entry) entry)) :
    TotalWP program (.letPrim value continuation) normal returned entry :=
  (letPrim_iff value continuation).mpr body

/-- Use a mathematical intermediate condition in a source sequence. -/
theorem seq {first second : Stmt signatures Γ result} {middle : Env Γ → Prop}
    (head : TotalWP program first middle returned entry)
    (tail : ∀ next, middle next → TotalWP program second normal returned next) :
    TotalWP program (.seq first second) normal returned entry :=
  (seq_iff first second).mpr (head.mono_post tail (fun _ _ h => h))

end TotalWP

/-- A source function returns a value satisfying an ordinary mathematical
relation on its arguments. Neither a fault nor body fallthrough is success. -/
def FunctionTotal {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) (pre : Env signatures[fn].params → Prop)
    (post : Env signatures[fn].params → Value signatures[fn].result → Prop) : Prop :=
  ∀ args, pre args → ∃ finish value,
    Exec program (program.body fn) args finish (.returned value) ∧ post args value

namespace FunctionTotal

variable {signatures : List Signature} {program : Program signatures}
variable {fn : Fin signatures.length}
variable {pre pre' : Env signatures[fn].params → Prop}
variable {post post' : Env signatures[fn].params → Value signatures[fn].result → Prop}

/-- Source body verification supplies actual successful function termination. -/
theorem of_wp (body : ∀ args, pre args →
    TotalWP program (program.body fn) (fun _ => False)
      (fun value _ => post args value) args) :
    FunctionTotal program fn pre post := by
  intro args hpre
  obtain ⟨finish, control, execution, hpost⟩ := body args hpre
  cases control with
  | normal => exact False.elim hpost
  | returned value => exact ⟨finish, value, execution, hpost⟩
  | fault fault => exact False.elim hpost

/-- A returned source execution is also a body WP proof. -/
theorem wp (h : FunctionTotal program fn pre post) (args : Env signatures[fn].params)
    (hpre : pre args) :
    TotalWP program (program.body fn) (fun _ => False)
      (fun value _ => post args value) args := by
  obtain ⟨finish, value, execution, hpost⟩ := h args hpre
  exact ⟨finish, .returned value, execution, hpost⟩

/-- Strengthen the source precondition and weaken the mathematical result relation. -/
theorem consequence (h : FunctionTotal program fn pre post)
    (hpre : ∀ args, pre' args → pre args)
    (hpost : ∀ args value, pre' args → post args value → post' args value) :
    FunctionTotal program fn pre' post' := by
  intro args input
  obtain ⟨finish, value, execution, output⟩ := h args (hpre args input)
  exact ⟨finish, value, execution, hpost args value input output⟩

/-- The mathematical postcondition describes any actual successful invocation,
not just the execution witness selected by a total-correctness proof. -/
theorem postcondition (h : FunctionTotal program fn pre post)
    {args finish : Env signatures[fn].params} {value : Value signatures[fn].result}
    (hpre : pre args)
    (execution : Exec program (program.body fn) args finish (.returned value)) :
    post args value := by
  obtain ⟨otherFinish, otherValue, otherExec, hpost⟩ := h args hpre
  have equal : otherValue = value := Control.returned.inj (otherExec.deterministic execution).2
  exact equal ▸ hpost

end FunctionTotal

namespace TotalWP

/-- Apply a source function's mathematical contract and bind its actual returned
value. The caller's lexical values, rather than the callee environment, continue. -/
theorem call {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {fn : Fin signatures.length}
    {args : Args Γ signatures[fn].params}
    {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : Env Γ → Prop} {returned : Value result → Env Γ → Prop} {entry : Env Γ}
    {pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop}
    (callee : FunctionTotal program fn pre post) (hpre : pre (args.eval entry))
    (body : ∀ value, post (args.eval entry) value →
      TotalWP program continuation (fun finish => normal (Env.tail finish))
        (fun result finish => returned result (Env.tail finish)) (Env.cons value entry)) :
    TotalWP program (.call fn args continuation) normal returned entry := by
  obtain ⟨calleeFinish, value, invocation, hpost⟩ := callee (args.eval entry) hpre
  obtain ⟨finish, control, execution, result⟩ := body value hpost
  exact ⟨Env.tail finish, control, .callReturn invocation execution, result⟩

end TotalWP

end Complexity.Language
