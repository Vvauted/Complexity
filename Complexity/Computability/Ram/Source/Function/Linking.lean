/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Time

/-!
# Callable functions under linking

A function-table embedding transports safe invocations, their returned values
and shared effects, and their exact compiled body counts. The caller-facing
contract therefore remains valid after calls in its implementation are renamed.
Changing the compiler's reserved-register boundary also preserves body counts.

Transporting a conditional time bound uses a separate source correctness
contract to obtain a source invocation. Its transported execution is compared
with the target execution by determinism. No reflection through a possibly
non-injective embedding is assumed, and time bounds are not used to establish
termination.
-/

namespace Ram.Source

/-- Linking preserves a safe invocation's arguments, returned fields and shared effects. -/
theorem FunctionExec.renameCalls {heapLimit depth : Nat} {source target : Program}
    {ρ : Nat → Nat} {f : Func} {args : List (Word w)}
    {entry finish : State w} {value : List (Word w)}
    (h : FunctionExec source heapLimit depth f args entry value finish)
    (embedding : Program.Embeds ρ source target) :
    FunctionExec target heapLimit depth (f.renameCalls ρ) args entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.renameCalls embedding, result, returned, shared⟩

/-- Linking preserves the actual compiled body count of the same invocation. -/
theorem FunctionMeasuredExec.renameCalls {control heapLimit depth bodySteps : Nat}
    {source target : Program} {ρ : Nat → Nat} {f : Func} {args : List (Word w)}
    {entry finish : State w} {value : List (Word w)}
    (h : FunctionMeasuredExec control source heapLimit depth f args bodySteps
      entry value finish)
    (embedding : Program.Embeds ρ source target) :
    FunctionMeasuredExec control target heapLimit depth (f.renameCalls ρ) args bodySteps
      entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.renameCalls embedding, result, returned, shared⟩

/-- The compiler's reserved-register boundary changes neither body count nor result. -/
theorem FunctionMeasuredExec.rebase {control heapLimit depth bodySteps : Nat}
    {program : Program} {f : Func} {args : List (Word w)}
    {entry finish : State w} {value : List (Word w)}
    (h : FunctionMeasuredExec control program heapLimit depth f args bodySteps
      entry value finish) (control' : Nat) :
    FunctionMeasuredExec control' program heapLimit depth f args bodySteps
      entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.rebase control', result, returned, shared⟩

/-- A callable correctness contract is unchanged when its implementation is linked. -/
theorem FunctionContract.renameCalls {heapLimit depth : Nat} {source target : Program}
    {ρ : Nat → Nat} {f : Func} {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    (h : FunctionContract source heapLimit depth f P Q)
    (embedding : Program.Embeds ρ source target) :
    FunctionContract target heapLimit depth (f.renameCalls ρ) P Q := by
  intro args entry hp
  obtain ⟨value, finish, execution, result⟩ := h args entry hp
  exact ⟨value, finish, execution.renameCalls embedding, result⟩

/-- Move a separate body-time bound to a different reserved-register boundary. -/
theorem FunctionTimeBound.rebase {control heapLimit depth : Nat} {program : Program}
    {f : Func} {P : List (Word w) → State w → Prop}
    {bound : List (Word w) → State w → Nat}
    (h : FunctionTimeBound control program heapLimit depth f P bound) (control' : Nat) :
    FunctionTimeBound control' program heapLimit depth f P bound :=
  fun args entry hp bodySteps value finish execution =>
    h args entry hp bodySteps value finish (execution.rebase control)

/-- A separately proved source contract supplies the invocation used to transport
a time bound. Determinism identifies its count with every target invocation;
the embedding need not support backwards execution transport. -/
theorem FunctionTimeBound.renameCalls {control heapLimit depth : Nat}
    {source target : Program} {ρ : Nat → Nat} {f : Func}
    {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    {bound : List (Word w) → State w → Nat}
    (h : FunctionTimeBound control source heapLimit depth f P bound)
    (embedding : Program.Embeds ρ source target)
    (correct : FunctionContract source heapLimit depth f P Q) :
    FunctionTimeBound control target heapLimit depth (f.renameCalls ρ) P bound := by
  intro args entry hp bodySteps value finish execution
  obtain ⟨sourceValue, sourceFinish, sourceExecution, _⟩ := correct args entry hp
  obtain ⟨sourceSteps, measured⟩ := sourceExecution.exists_measured control
  have count := (execution.deterministic (measured.renameCalls embedding)).1
  rw [count]
  exact h args entry hp sourceSteps sourceValue sourceFinish measured

end Ram.Source
