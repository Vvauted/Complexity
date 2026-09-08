/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Function
import Complexity.Computability.Ram.Verification.Time.Basic

/-!
# Compiler-derived function costs

`Ram.Source.FunctionMeasuredExec` observes the same invocation as
`Ram.Source.FunctionExec`, with the exact compiled count of its body. This count
includes calls performed by the body, but not the enclosing caller's argument
evaluation, frame setup or return sequence. `Ram.Source.FunctionMeasuredExec.call`
adds those actual generated blocks when the function is invoked at a call site.

`Ram.Source.FunctionTimeBound` is a separate conditional bound on body execution.
Combining it with `Ram.Source.FunctionContract` establishes termination, the
functional postcondition and the bound for one and the same invocation.
The count is independent of the proposed bound and safety capacities.
-/

namespace Ram.Source

/-- Function invocation with its exact compiled body count. The returned fields
and shared effects are those of the same body; enclosing call overhead is
accounted for by `FunctionMeasuredExec.call`, not included in `bodySteps`. -/
def FunctionMeasuredExec (control : Nat) (program : Program) (heapLimit depth : Nat)
    (f : Func) (args : List (Word w)) (bodySteps : Nat)
    (entry : State w) (value : List (Word w)) (finish : State w) : Prop :=
  args.length = f.params ∧ f.params ≤ f.locals ∧
    ∃ callee,
      LocalMeasuredExec control program heapLimit depth f.body bodySteps
        (entry.enter args) callee ∧
      (∀ result ∈ f.results, result.ReadsBelow heapLimit callee.regs callee.mem) ∧
      value = f.results.map callee.eval ∧ finish = entry.restore callee

namespace FunctionMeasuredExec

variable {w control heapLimit depth bodySteps : Nat} {program : Program} {f : Func}
variable {args : List (Word w)} {entry finish : State w} {value : List (Word w)}

/-- Reuse the existing measured body without choosing a cost annotation. -/
theorem of_body {callee : State w} (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (body : LocalMeasuredExec control program heapLimit depth f.body bodySteps
      (entry.enter args) callee)
    (result : ∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) :
    FunctionMeasuredExec control program heapLimit depth f args bodySteps entry
      (f.results.map callee.eval) (entry.restore callee) :=
  ⟨arity, frame, callee, body, result, rfl, rfl⟩

/-- Erasing the count retains the same safe invocation. -/
theorem erase
    (h : FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    FunctionExec program heapLimit depth f args entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.erase, result, returned, shared⟩

/-- Measuring the body does not change the number of returned fields. -/
theorem length_eq
    (h : FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) :
    value.length = f.results.length :=
  h.erase.length_eq

/-- A body has one count and one result, independently of safety capacities
and the compiler's reserved-register boundary. -/
theorem deterministic {control' heapLimit' depth' bodySteps' : Nat}
    {value' : List (Word w)} {finish' : State w}
    (h : FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish)
    (h' : FunctionMeasuredExec control' program heapLimit' depth' f args bodySteps'
      entry value' finish') :
    bodySteps = bodySteps' ∧ value = value' ∧ finish = finish' := by
  obtain ⟨_, _, callee, body, _, rfl, rfl⟩ := h
  obtain ⟨_, _, callee', body', _, rfl, rfl⟩ := h'
  obtain ⟨count, same⟩ := body.deterministic (body'.rebase control)
  subst callee'
  exact ⟨count, rfl, rfl⟩

/-- Count an actual call, including argument evaluation, frame code, the entry
jump, the callee body, return code and every result-field receipt. -/
theorem call {fn : Nat} {dsts : List Reg} {exprs : List Expr}
    (h : FunctionMeasuredExec control program heapLimit depth f
      (exprs.map entry.eval) bodySteps entry value finish)
    (lookup : program[fn]? = some f)
    (resultCount : dsts.length = f.results.length)
    (arguments : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem) :
    LocalMeasuredExec control program heapLimit (depth + 1) (.call dsts fn exprs)
      ((ABI.callPrefixLocals control f.locals exprs 0).length + 1 + bodySteps +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length)
      entry (finish.setRegs dsts value) := by
  obtain ⟨arity, frame, callee, body, result, rfl, rfl⟩ := h
  rw [State.restore_setRegs]
  exact .call lookup (by simpa only [List.length_map] using arity) resultCount frame
    arguments body result

end FunctionMeasuredExec

/-- Safe termination already determines an actual body count; a time bound
is not needed to obtain the corresponding measured invocation. -/
theorem FunctionExec.exists_measured {heapLimit depth : Nat} {program : Program} {f : Func}
    {args : List (Word w)} {entry finish : State w} {value : List (Word w)}
    (h : FunctionExec program heapLimit depth f args entry value finish) (control : Nat) :
    ∃ bodySteps, FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  obtain ⟨bodySteps, measured⟩ := body.exists_localMeasured control
  exact ⟨bodySteps, arity, frame, callee, measured, result, returned, shared⟩

/-- A conditional bound on the actual body count. This does not assert
termination; use `FunctionContract.with_timeBound` for a total guarantee. -/
def FunctionTimeBound (control : Nat) (program : Program) (heapLimit depth : Nat) (f : Func)
    (P : List (Word w) → State w → Prop) (bound : List (Word w) → State w → Nat) : Prop :=
  ∀ args entry, P args entry → ∀ bodySteps value finish,
    FunctionMeasuredExec control program heapLimit depth f args bodySteps entry value finish →
      bodySteps ≤ bound args entry

namespace FunctionTimeBound

variable {w control heapLimit depth : Nat} {program : Program} {f : Func}
variable {P : List (Word w) → State w → Prop}
variable {bound bound' : List (Word w) → State w → Nat}

/-- Transfer an existing body-time proof through the argument representation.
No functional specification or proposed result is used to define the count. -/
theorem of_body {R : State w → Prop} {bodyBound : State w → Nat}
    (body : TimeBound control program heapLimit depth f.body R bodyBound)
    (pre : ∀ args entry, P args entry → R (entry.enter args))
    (budget : ∀ args entry, P args entry → bodyBound (entry.enter args) ≤ bound args entry) :
    FunctionTimeBound control program heapLimit depth f P bound := by
  intro args entry hp bodySteps value finish invocation
  obtain ⟨_, _, callee, execution, _, _, _⟩ := invocation
  exact Nat.le_trans (body _ (pre args entry hp) bodySteps callee execution)
    (budget args entry hp)

theorem mono_bound (h : FunctionTimeBound control program heapLimit depth f P bound)
    (budget : ∀ args entry, P args entry → bound args entry ≤ bound' args entry) :
    FunctionTimeBound control program heapLimit depth f P bound' :=
  fun args entry hp bodySteps value finish execution =>
    Nat.le_trans (h args entry hp bodySteps value finish execution) (budget args entry hp)

end FunctionTimeBound

/-- Attach a separate bound to the very invocation supplied by correctness. -/
theorem FunctionContract.with_timeBound {control heapLimit depth : Nat} {program : Program}
    {f : Func} {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    {bound : List (Word w) → State w → Nat}
    (h : FunctionContract program heapLimit depth f P Q)
    (time : FunctionTimeBound control program heapLimit depth f P bound) :
    ∀ args entry, P args entry → ∃ bodySteps value finish,
      FunctionMeasuredExec control program heapLimit depth f args bodySteps entry value finish ∧
      Q args entry value finish ∧ bodySteps ≤ bound args entry := by
  intro args entry hp
  obtain ⟨value, finish, execution, result⟩ := h args entry hp
  obtain ⟨bodySteps, measured⟩ := execution.exists_measured control
  exact ⟨bodySteps, value, finish, measured, result,
    time args entry hp bodySteps value finish measured⟩

end Ram.Source
