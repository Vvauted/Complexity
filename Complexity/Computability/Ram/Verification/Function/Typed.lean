/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Value

/-!
# Typed correctness statements for the same callable functions

`Ram.Source.TypedFunctionContract` states mathematical properties of typed
arguments and returned values. It is a representation view of `FunctionExec`:
the implementation, shared effects and termination relation are unchanged.
Encoding an array reference exposes its existing base and length, not a loader.

The body and call rules keep field decoding out of algorithmic proofs. `raw`
recovers an ordinary function contract at a chosen typed input for existing
independent time rules; it requires no claim that arbitrary raw inputs decode.
`Ram.Func.evalTyped` is the shared typed projection used by source declarations.
No correctness rule requires an instruction budget.
-/

namespace Ram

namespace Func

/-- Decode the actual semantic result using the function's declared result shape. -/
noncomputable def evalTyped (f : Func) (kind : DSL.ValueKind)
    (shape : f.results.length = kind.width) (program : Program) (heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) :
    Part (kind.Value w × Source.State w) :=
  (f.evalFields program heapLimit args entry).map fun result =>
    (kind.decode result.1.val (result.1.property.trans shape), result.2)

/-- The typed projection reuses a result equation of the original invocation. -/
theorem evalTyped_eq_some {f : Func} {kind : DSL.ValueKind} {program : Program}
    {heapLimit : Nat} {args : List (Word w)} {entry finish : Source.State w}
    {value : kind.Value w} (shape : f.results.length = kind.width)
    (h : f.eval program heapLimit args entry = Part.some (kind.encode value, finish)) :
    f.evalTyped kind shape program heapLimit args entry = Part.some (value, finish) := by
  have fields := evalFields_eq_some h ((kind.length_encode value).trans shape.symm)
  simp only [evalTyped, fields, Part.map_some, DSL.ValueKind.decode_encode]

end Func

namespace Source

/-- A typed value equation follows from the same raw source invocation. -/
theorem FunctionExec.evalTyped_eq_some {program : Program} {heapLimit depth : Nat}
    {f : Func} {kind : DSL.ValueKind} {args : List (Word w)}
    {entry finish : State w} {value : kind.Value w}
    (h : FunctionExec program heapLimit depth f args entry (kind.encode value) finish)
    (shape : f.results.length = kind.width) :
    f.evalTyped kind shape program heapLimit args entry = Part.some (value, finish) :=
  Func.evalTyped_eq_some shape h.eval_eq_some

/-- Total correctness at typed inputs and outputs of one existing source function.
The argument encoder describes its runtime fields; the postcondition can use
ordinary mathematical objects without defining another implementation. -/
def TypedFunctionContract {α : Type*} (program : Program) (heapLimit depth : Nat)
    (f : Func) (kind : DSL.ValueKind) (encodeArgs : α → List (Word w))
    (P : α → State w → Prop) (Q : α → State w → kind.Value w → State w → Prop) : Prop :=
  ∀ arg entry, P arg entry → ∃ value finish,
    FunctionExec program heapLimit depth f (encodeArgs arg) entry (kind.encode value) finish ∧
      Q arg entry value finish

namespace TypedFunctionContract

variable {α : Type*} {w heapLimit depth : Nat} {program : Program} {f : Func}
variable {kind : DSL.ValueKind} {encodeArgs : α → List (Word w)}
variable {P P' : α → State w → Prop}
variable {Q Q' : α → State w → kind.Value w → State w → Prop}

/-- Prove a typed postcondition directly about the body's actual returned fields.
All field expressions are evaluated in the same final callee state. -/
theorem of_wp (shape : f.results.length = kind.width)
    (arity : ∀ arg entry, P arg entry → (encodeArgs arg).length = f.params)
    (frame : f.params ≤ f.locals)
    (body : ∀ arg entry, P arg entry →
      Verification.TotalWP program heapLimit depth f.body
        (fun callee =>
          (∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) ∧
          Q arg entry
            (kind.decode (f.results.map callee.eval) (by simpa only [List.length_map] using shape))
            (entry.restore callee)) (entry.enter (encodeArgs arg))) :
    TypedFunctionContract program heapLimit depth f kind encodeArgs P Q := by
  intro arg entry pre
  obtain ⟨callee, execution, reads, post⟩ := body arg entry pre
  refine ⟨_, _, ?_, post⟩
  simpa only [DSL.ValueKind.encode_decode] using
    (FunctionExec.of_body (arity arg entry pre) frame execution reads)

/-- Reuse a raw contract through the declared result shape. The adapter sees
typed values, so clients need not split a result list or manufacture fields. -/
theorem of_raw {R : List (Word w) → State w → Prop}
    {S : List (Word w) → State w → List (Word w) → State w → Prop}
    (shape : f.results.length = kind.width)
    (contract : FunctionContract program heapLimit depth f R S)
    (pre : ∀ arg entry, P arg entry → R (encodeArgs arg) entry)
    (post : ∀ arg entry value finish, P arg entry →
      S (encodeArgs arg) entry (kind.encode value) finish → Q arg entry value finish) :
    TypedFunctionContract program heapLimit depth f kind encodeArgs P Q := by
  intro arg entry hp
  obtain ⟨fields, finish, execution, result⟩ := contract _ entry (pre arg entry hp)
  let value := kind.decode fields (execution.length_eq.trans shape)
  have encoded : kind.encode value = fields := kind.encode_decode fields _
  refine ⟨value, finish, ?_, post arg entry value finish hp ?_⟩
  · simpa only [encoded] using execution
  · simpa only [encoded] using result

/-- Recover the original contract at one chosen typed input. No surjectivity
of the input representation, and no time bound, is assumed. -/
theorem raw (h : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (arg : α) :
    FunctionContract program heapLimit depth f
      (fun args entry => args = encodeArgs arg ∧ P arg entry)
      (fun _ entry fields finish =>
        ∃ value, fields = kind.encode value ∧ Q arg entry value finish) := by
  rintro args entry ⟨rfl, pre⟩
  obtain ⟨value, finish, execution, post⟩ := h arg entry pre
  exact ⟨kind.encode value, finish, execution, value, rfl, post⟩

theorem consequence
    (h : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (pre : ∀ arg entry, P' arg entry → P arg entry)
    (post : ∀ arg entry value finish, P' arg entry → Q arg entry value finish →
      Q' arg entry value finish) :
    TypedFunctionContract program heapLimit depth f kind encodeArgs P' Q' := by
  intro arg entry hp
  obtain ⟨value, finish, execution, result⟩ := h arg entry (pre arg entry hp)
  exact ⟨value, finish, execution, post arg entry value finish hp result⟩

/-- Every actual invocation at the same represented input satisfies the typed
postcondition, independently of its safety capacities. -/
theorem post {heapLimit' depth' : Nat} {arg : α} {entry finish : State w}
    {value : kind.Value w}
    (h : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (pre : P arg entry)
    (execution : FunctionExec program heapLimit' depth' f (encodeArgs arg) entry
      (kind.encode value) finish) : Q arg entry value finish := by
  obtain ⟨value', finish', run, result⟩ := h arg entry pre
  obtain ⟨equal, rfl⟩ := run.deterministic execution
  have same : value' = value := kind.encode_injective equal
  simpa only [same] using result

/-- Call the same implementation, passing a typed result to the continuation.
Receipt still performs the actual ordered destination updates. -/
theorem wp_call {fn callDepth : Nat} {arg : α} {dsts : List Reg} {exprs : List Expr}
    {entry : State w} {post : State w → Prop}
    (h : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (lookup : program[fn]? = some f) (resultCount : dsts.length = f.results.length)
    (arguments : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (argumentValues : exprs.map entry.eval = encodeArgs arg)
    (pre : P arg entry) (nesting : depth + 1 ≤ callDepth)
    (continuation : ∀ value finish, Q arg entry value finish →
      finish.regs = entry.regs → post (finish.setRegs dsts (kind.encode value))) :
    Verification.TotalWP program heapLimit callDepth (.call dsts fn exprs) post entry := by
  obtain ⟨value, finish, execution, result⟩ := h arg entry pre
  have invocation : FunctionExec program heapLimit depth f (exprs.map entry.eval) entry
      (kind.encode value) finish := by
    simpa only [argumentValues] using execution
  exact ⟨_, (invocation.call lookup resultCount arguments).mono nesting,
    continuation value finish result execution.regs_eq⟩

/-- Typed semantic equations inherit both termination and the mathematical
postcondition from the same implementation contract. -/
theorem eval_spec {arg : α} {entry : State w}
    (h : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (shape : f.results.length = kind.width) (pre : P arg entry) :
    ∃ value finish,
      f.evalTyped kind shape program heapLimit (encodeArgs arg) entry = Part.some (value, finish) ∧
        Q arg entry value finish := by
  obtain ⟨value, finish, execution, post⟩ := h arg entry pre
  exact ⟨value, finish, execution.evalTyped_eq_some shape, post⟩

end TypedFunctionContract

end Source
end Ram
