/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Basic
import Complexity.Language.Verification
import Mathlib.Logic.Equiv.Defs

/-!
# Source functions on a mathematical input array

`ArrayFunction` selects one declared function with a borrowed natural-array
parameter and a natural result. The input is one private, initially populated
source object. `Returns` observes the existing source evaluation of that same
function; it neither extracts a value from a desired specification nor adds an
interpreter. The function may mutate, allocate or reclaim private storage.

`Correct` states a mathematical input/output property independently of machine
width, storage and time budgets. Preparing this private array is an invocation
boundary, not a claim that loading or copying input is free executable work.
-/

namespace Complexity.Language

/-- One fixed source function, selected from any typed declaration family. -/
structure ArrayFunction where
  signatures : List Signature
  program : Program signatures
  fn : Fin signatures.length
  parameterTypes : (signatures[fn.val]'fn.isLt).params = [.buffer .nat]
  resultType : (signatures[fn.val]'fn.isLt).result = .nat

namespace ArrayFunction

/-- Select a generated function by its existing signature, without wrapping or
replacing its body. -/
def ofProgram {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length)
    (signature : (signatures[fn.val]'fn.isLt) = ⟨[.buffer .nat], .nat⟩) : ArrayFunction where
  signatures := signatures
  program := program
  fn := fn
  parameterTypes := congrArg Signature.params signature
  resultType := congrArg Signature.result signature

/-- The sole input view covers the whole initial object. -/
def inputBuffer (xs : Array Nat) : Buffer .nat := ⟨0, 0, xs.size⟩

/-- The fixed source input representation, independent of the candidate and answer. -/
def inputHeap (xs : Array Nat) : Heap := ⟨#[⟨.nat, xs⟩]⟩

/-- The fixed source argument contains only the input view. -/
def inputArgs (xs : Array Nat) : Env [.buffer .nat] :=
  Env.cons (inputBuffer xs) Env.empty

/-- The canonical input view has exactly the supplied mathematical contents. -/
theorem inputBuffer_contents (xs : Array Nat) :
    (inputBuffer xs).Contents (inputHeap xs) xs := by
  refine ⟨xs, ?_, by simp [inputBuffer], ?_⟩
  · apply Heap.object?_eq_some_iff.mpr
    rfl
  · simp [inputBuffer]

/-- Transport the canonical input through the selected function's signature. -/
def args (f : ArrayFunction) (xs : Array Nat) : Env f.signatures[f.fn].params :=
  cast (congrArg Env f.parameterTypes.symm) (inputArgs xs)

/-- The declared result is a natural number; this equivalence only transports
its type and performs no specification-dependent decoding. -/
def resultEquiv (f : ArrayFunction) : Value f.signatures[f.fn].result ≃ Nat :=
  Equiv.cast (congrArg Value f.resultType)

/-- Successful evaluation of the selected source function on the fixed input.
The final private heap is unconstrained, but the returned value is exact. -/
def Returns (f : ArrayFunction) (xs : Array Nat) (result : Nat) : Prop :=
  ∃ heap, f.program.eval f.fn (f.args xs) (inputHeap xs) =
    Part.some (.ok (f.resultEquiv.symm result), heap)

/-- Ordinary mathematical correctness for every legal input, with successful
source termination and no machine or cost premise. -/
def Correct (f : ArrayFunction) (valid : Array Nat → Prop)
    (answer : Array Nat → Nat) : Prop :=
  ∀ xs, valid xs → f.Returns xs (answer xs)

/-- Reuse an existing function contract on the canonical input. The shared
rule handles source evaluation and result-type transport; no per-task machine
or evaluator adapter is required. -/
theorem Returns.of_total {f : ArrayFunction} {xs : Array Nat} {result : Nat}
    {pre : Env f.signatures[f.fn].params → Heap → Prop}
    {post : Env f.signatures[f.fn].params → Heap →
      Value f.signatures[f.fn].result → Heap → Prop}
    (specification : FunctionTotal f.program f.fn pre post)
    (input : pre (f.args xs) (inputHeap xs))
    (output : ∀ value heap, post (f.args xs) (inputHeap xs) value heap →
      f.resultEquiv value = result) : f.Returns xs result := by
  obtain ⟨finish, value, execution, property⟩ :=
    specification (f.args xs) (inputHeap xs) input
  have returned : value = f.resultEquiv.symm result := by
    apply f.resultEquiv.injective
    simpa only [Equiv.apply_symm_apply] using output value finish.heap property
  refine ⟨finish.heap, ?_⟩
  rw [← returned]
  exact Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩

/-- Publish a supplied ordinary source contract as mathematical array
correctness. Canonical input contents are provided by `inputBuffer_contents`. -/
theorem Correct.of_total {f : ArrayFunction} {valid : Array Nat → Prop}
    {answer : Array Nat → Nat}
    {pre : Env f.signatures[f.fn].params → Heap → Prop}
    {post : Env f.signatures[f.fn].params → Heap →
      Value f.signatures[f.fn].result → Heap → Prop}
    (specification : FunctionTotal f.program f.fn pre post)
    (input : ∀ xs, valid xs → pre (f.args xs) (inputHeap xs))
    (output : ∀ xs, valid xs → ∀ value heap,
      post (f.args xs) (inputHeap xs) value heap → f.resultEquiv value = answer xs) :
    f.Correct valid answer :=
  fun xs legal => Returns.of_total specification (input xs legal) (output xs legal)

/-- Any actual evaluation of this source function has its specified result. -/
theorem Returns.result_eq {f : ArrayFunction} {xs : Array Nat} {result : Nat}
    (specified : f.Returns xs result)
    {value : Value f.signatures[f.fn].result} {heap : Heap}
    (evaluated : f.program.eval f.fn (f.args xs) (inputHeap xs) = Part.some (.ok value, heap)) :
    f.resultEquiv value = result := by
  obtain ⟨expectedHeap, expected⟩ := specified
  have same := Part.some_injective (evaluated.symm.trans expected)
  have returned := Except.ok.inj (congrArg Prod.fst same)
  rw [returned, Equiv.apply_symm_apply]

/-- The result relation cannot certify two different answers for one input. -/
theorem Returns.unique {f : ArrayFunction} {xs : Array Nat} {left right : Nat}
    (first : f.Returns xs left) (second : f.Returns xs right) : left = right := by
  obtain ⟨heap, evaluated⟩ := second
  simpa only [Equiv.apply_symm_apply] using (first.result_eq evaluated).symm

end ArrayFunction

end Complexity.Language
