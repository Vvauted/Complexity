/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Basic
import Complexity.Computability.Ram.Source.Linking
import Complexity.Computability.Ram.Verification.Total

/-!
# Correctness statements for callable functions

`Ram.Source.FunctionContract` states a relation between arguments, the actual
returned fields and shared state. It requires neither a `main` program nor a
second mathematical implementation. Ordinary mathematical properties and
representation predicates can be used directly in the postcondition.

`FunctionContract.of_wp` proves the desired postcondition directly from the body;
`of_body` reuses an existing `Ram.Source.TotalRelContract`. The call rule uses the
same executable function through `Ram.Source.FunctionExec.call`. These rules
impose no time bound and do not assume unchanged memory or input/output.
-/

namespace Ram.Source

/-- Additional heap capacity preserves the same invocation and shared effects. -/
theorem FunctionExec.mono_heap {heapLimit heapLimit' depth : Nat} {program : Program}
    {f : Func} {args : List (Word w)} {entry finish : State w} {value : List (Word w)}
    (h : FunctionExec program heapLimit depth f args entry value finish)
    (hh : heapLimit ≤ heapLimit') :
    FunctionExec program heapLimit' depth f args entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.mono_heap hh,
    fun expr hmem => (result expr hmem).mono_heap hh, returned, shared⟩

/-- Total correctness of a function, stated on arguments, return fields and
shared effects. The precondition may express representations and safety facts. -/
def FunctionContract (program : Program) (heapLimit depth : Nat) (f : Func)
    (P : List (Word w) → State w → Prop)
    (Q : List (Word w) → State w → List (Word w) → State w → Prop) : Prop :=
  ∀ args entry, P args entry → ∃ value finish,
    FunctionExec program heapLimit depth f args entry value finish ∧ Q args entry value finish

namespace FunctionContract

variable {w heapLimit depth : Nat} {program : Program} {f : Func}
variable {P P' : List (Word w) → State w → Prop}
variable {Q Q' : List (Word w) → State w → List (Word w) → State w → Prop}

/-- Prove a function directly from its arguments and desired postcondition.
The body starts with the actual parameter bindings, and its return fields
and shared effects are substituted into the same postcondition. No separate
body representation relation or time budget is required. -/
theorem of_wp (arity : ∀ args entry, P args entry → args.length = f.params)
    (frame : f.params ≤ f.locals)
    (body : ∀ args entry, P args entry →
      Verification.TotalWP program heapLimit depth f.body
        (fun callee =>
          (∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) ∧
          Q args entry (f.results.map callee.eval) (entry.restore callee)) (entry.enter args)) :
    FunctionContract program heapLimit depth f P Q := by
  intro args entry hp
  obtain ⟨callee, execution, reads, result⟩ := body args entry hp
  exact ⟨_, _, FunctionExec.of_body (arity args entry hp) frame execution reads, result⟩

/-- Reuse a body contract with a representation adapter at entry and return.
The adapter proves a property of the actual return fields, not a separate
implementation. Caller locals are restored by `State.restore`. -/
theorem of_body {R : State w → Prop} {S : State w → State w → Prop}
    (body : TotalRelContract program heapLimit depth f.body R
      (fun entered callee =>
        (∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) ∧
        S entered callee))
    (arity : ∀ args entry, P args entry → args.length = f.params)
    (frame : f.params ≤ f.locals)
    (pre : ∀ args entry, P args entry → R (entry.enter args))
    (post : ∀ args entry, P args entry → ∀ callee, S (entry.enter args) callee →
      Q args entry (f.results.map callee.eval) (entry.restore callee)) :
    FunctionContract program heapLimit depth f P Q := by
  intro args entry hp
  obtain ⟨callee, execution, reads, result⟩ := body _ (pre args entry hp)
  exact ⟨_, _, FunctionExec.of_body (arity args entry hp) frame execution reads,
    post args entry hp callee result⟩

theorem consequence (h : FunctionContract program heapLimit depth f P Q)
    (pre : ∀ args entry, P' args entry → P args entry)
    (post : ∀ args entry value finish, P' args entry → Q args entry value finish →
      Q' args entry value finish) :
    FunctionContract program heapLimit depth f P' Q' := by
  intro args entry hp
  obtain ⟨value, finish, execution, result⟩ := h args entry (pre args entry hp)
  exact ⟨value, finish, execution, post args entry value finish hp result⟩

/-- A total specification holds of every execution of the same function. -/
theorem post {heapLimit' depth' : Nat} {args : List (Word w)}
    {entry finish : State w} {value : List (Word w)}
    (h : FunctionContract program heapLimit depth f P Q) (pre : P args entry)
    (execution : FunctionExec program heapLimit' depth' f args entry value finish) :
    Q args entry value finish := by
  obtain ⟨value', finish', run, result⟩ := h args entry pre
  obtain ⟨rfl, rfl⟩ := run.deterministic execution
  exact result

/-- Invoke a proved function without unfolding its body or callee frame.
The continuation sees the returned fields, actual shared effects and restored
caller locals. Local preservation need not be added to the user postcondition. -/
theorem wp_call {fn callDepth : Nat} {dsts : List Reg} {exprs : List Expr} {entry : State w}
    {post : State w → Prop} (h : FunctionContract program heapLimit depth f P Q)
    (lookup : program[fn]? = some f)
    (resultCount : dsts.length = f.results.length)
    (arguments : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (pre : P (exprs.map entry.eval) entry) (nesting : depth + 1 ≤ callDepth)
    (continuation : ∀ value finish, Q (exprs.map entry.eval) entry value finish →
      finish.regs = entry.regs → post (finish.setRegs dsts value)) :
    Verification.TotalWP program heapLimit callDepth (.call dsts fn exprs) post entry := by
  obtain ⟨value, finish, execution, result⟩ := h _ entry pre
  exact ⟨_, (execution.call lookup resultCount arguments).mono nesting,
    continuation value finish result execution.regs_eq⟩

end FunctionContract

end Ram.Source
