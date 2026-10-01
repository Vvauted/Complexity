/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.RepresentedFunction

/-!
# Persistent sessions of source function calls

A session selects initialization and step entries of one existing source program.
Only initialization receives the configuration. Each step receives the previous
actual state value and the current request; it starts in the previous actual heap.
The environment's request sequence is proof data, never a source argument.

This is a connection-layer interface, not another evaluator or a new source
construct. Successful calls use `Program.eval`; faulting or divergent calls do
not satisfy these total-success relations. Correctness and termination have no
machine-width or budget premise. RAM realization is a separate module.

Replies retain their return-time heap as a mathematical observation. This does
not copy or freeze mutable storage at runtime, nor promise that a returned
reference will still have the same contents after a later step.
-/

namespace Complexity.Language

/-- Two actual entries with a private runtime state. Configuration and request
layouts are fixed by the protocol; the implementation chooses its state type. -/
structure Session (configuration request : List Ty) (response : Ty) where
  signatures : List Signature
  program : Program signatures
  stateTy : Ty
  init : Fin signatures.length
  step : Fin signatures.length
  init_signature : signatures[init] = ⟨configuration, stateTy⟩
  step_signature : signatures[step] = ⟨stateTy :: request, .prod response stateTy⟩

namespace Session

variable {configuration request : List Ty} {response : Ty}
variable (session : Session configuration request response)

/-- The same initialization arguments at the selected entry's signature. -/
def initArgs (args : Env configuration) : Env session.signatures[session.init].params :=
  cast (congrArg Env (congrArg Signature.params session.init_signature).symm) args

/-- Pass the actual retained state, without reloading its mathematical contents. -/
def stepArgs (state : Value session.stateTy) (input : Env request) :
    Env session.signatures[session.step].params :=
  cast (congrArg Env (congrArg Signature.params session.step_signature).symm)
    (Env.cons state input)

/-- Signature transport of the initializer's actual returned state. -/
def initValue (state : Value session.stateTy) :
    Value session.signatures[session.init].result :=
  cast (congrArg Value (congrArg Signature.result session.init_signature).symm) state

/-- Signature transport of a reply and its actual retained state. -/
def stepValue (reply : Value response) (state : Value session.stateTy) :
    Value session.signatures[session.step].result :=
  cast (congrArg Value (congrArg Signature.result session.step_signature).symm) (reply, state)

/-- Successful initialization of this selected source entry, in the supplied
initial heap. Loading the public configuration is a separate boundary. -/
def Starts (args : Env configuration) (heap : Heap)
    (state : Value session.stateTy) (finish : Heap) : Prop :=
  session.program.eval session.init (session.initArgs args) heap =
    Part.some (.ok (session.initValue state), finish)

/-- One successful actual step. Neither future requests nor a mathematical
state encoder occur in the invocation. -/
def Step (state : Value session.stateTy) (heap : Heap) (input : Env request)
    (reply : Value response) (next : Value session.stateTy) (finish : Heap) : Prop :=
  session.program.eval session.step (session.stepArgs state input) heap =
    Part.some (.ok (session.stepValue reply next), finish)

/-- A finite sequence of successful calls, threading the exact state and heap.
Each reply is observed at its own return-time heap, not the final session heap. -/
inductive Run : Value session.stateTy → Heap → List (Env request) →
    List (Value response × Heap) → Value session.stateTy → Heap → Prop
  | nil (state heap) : Run state heap [] [] state heap
  | cons {state heap input reply next intermediate inputs replies finish finalHeap}
      (step : session.Step state heap input reply next intermediate)
      (rest : Run next intermediate inputs replies finish finalHeap) :
      Run state heap (input :: inputs) ((reply, intermediate) :: replies) finish finalHeap

/-- Initialization happens once, including for an empty request sequence. -/
def Runs (args : Env configuration) (heap : Heap) (inputs : List (Env request))
    (replies : List (Value response × Heap)) (finish : Value session.stateTy)
    (finalHeap : Heap) : Prop :=
  ∃ state initialized, session.Starts args heap state initialized ∧
    session.Run state initialized inputs replies finish finalHeap

variable {session}

/-- A successful call has one actual reply, state and final heap. -/
theorem Step.deterministic
    {state : Value session.stateTy} {heap : Heap} {input : Env request}
    {reply₁ reply₂ : Value response} {next₁ next₂ : Value session.stateTy}
    {finish₁ finish₂ : Heap}
    (first : session.Step state heap input reply₁ next₁ finish₁)
    (second : session.Step state heap input reply₂ next₂ finish₂) :
    reply₁ = reply₂ ∧ next₁ = next₂ ∧ finish₁ = finish₂ := by
  have same := Part.some_injective (first.symm.trans second)
  have values := Except.ok.inj (congrArg Prod.fst same)
  have pair : (reply₁, next₁) = (reply₂, next₂) := by
    exact (Equiv.cast _).injective values
  exact ⟨congrArg Prod.fst pair, congrArg Prod.snd pair, congrArg Prod.snd same⟩

/-- Concatenation uses the actual state and heap at the boundary, not a fresh
invocation reconstructed from a mathematical state. -/
theorem Run.append
    {state middle finish : Value session.stateTy} {heap intermediate finalHeap : Heap}
    {inputs₁ inputs₂ : List (Env request)}
    {replies₁ replies₂ : List (Value response × Heap)}
    (first : session.Run state heap inputs₁ replies₁ middle intermediate)
    (second : session.Run middle intermediate inputs₂ replies₂ finish finalHeap) :
    session.Run state heap (inputs₁ ++ inputs₂) (replies₁ ++ replies₂) finish finalHeap := by
  induction first with
  | nil => exact second
  | cons step rest ih => exact .cons step (ih second)

/-- Every successful step contributes exactly one return-time reply. -/
theorem Run.length
    {state finish : Value session.stateTy} {heap finalHeap : Heap}
    {inputs : List (Env request)} {replies : List (Value response × Heap)}
    (run : session.Run state heap inputs replies finish finalHeap) :
    replies.length = inputs.length := by
  induction run with
  | nil => rfl
  | cons step rest ih => exact congrArg Nat.succ ih

/-- Compose ordinary source invariants and total step contracts without any
resource premise. The invariant may describe actual mutable contents. -/
theorem Run.exists_of_step
    (invariant : Value session.stateTy → Heap → Prop)
    (admissible : Env request → Prop)
    (total : ∀ state heap input, invariant state heap → admissible input →
      ∃ reply next finish, session.Step state heap input reply next finish ∧
        invariant next finish)
    {state : Value session.stateTy} {heap : Heap}
    (initial : invariant state heap) (inputs : List (Env request))
    (legal : ∀ input ∈ inputs, admissible input) :
    ∃ replies finish finalHeap,
      session.Run state heap inputs replies finish finalHeap ∧ invariant finish finalHeap := by
  induction inputs generalizing state heap with
  | nil => exact ⟨[], state, heap, .nil _ _, initial⟩
  | cons input inputs ih =>
      obtain ⟨reply, next, intermediate, step, preserved⟩ :=
        total state heap input initial (legal input (by simp))
      obtain ⟨replies, finish, finalHeap, rest, final⟩ :=
        ih preserved (fun input member => legal input (by simp [member]))
      exact ⟨(reply, intermediate) :: replies, finish, finalHeap, .cons step rest, final⟩

end Session
end Complexity.Language
