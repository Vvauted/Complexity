/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Basic
import Complexity.Language.ArrayFunction

/-!
# Fixed mathematical inputs and outputs

The source input instances choose one initial heap and argument environment for
each mathematical input. Scalars start in an empty heap; natural arrays reuse
the established single-array invocation boundary. Scalar prefixes add arguments
without changing the remaining input's heap or copying its contents.

`Input.comap` registers an injective presentation of an existing input layout.
Neither it nor `Input.ofEmbedding` implements arbitrary Lean transformations in
the source language or makes their execution free. Input preparation remains an
external invocation boundary. General combinations of independently heap-backed
inputs require their own fixed layout and representation proof.

Output instances only select existing structural representations of the actual
returned value and final heap. They depend on the result type, not on a proposed
answer, correctness theorem, or particular input. In particular an array output
observes return-time contents; it does not establish persistent ownership.
-/

namespace Complexity.Program

open Language

universe u v

namespace Input

/-- Heap-free inputs begin with no source objects. -/
def emptyHeap : Heap := ⟨#[]⟩

/-- Register an injective single-argument input presentation at an empty heap.
The embedding is an invocation boundary, not a source operation or loader. -/
def ofEmbedding {α : Type u} {τ : Ty} (encoding : α ↪ Value τ) : Input α where
  params := [τ]
  heap _ := emptyHeap
  args x := Env.cons (encoding x) Env.empty
  representation := ArgumentRepresentation.single (Representation.ofEmbedding encoding)
  represented _ := rfl

/-- Prepend one heap-independent field while retaining the other input's exact
heap. This registers a parameter layout; it performs no source-level copying. -/
def consScalar {α : Type u} {β : Type v} {τ : Ty}
    (encoding : α ↪ Value τ) (tail : Input β) : Input (α × β) where
  params := τ :: @Input.params β tail
  heap x := @Input.heap β tail x.2
  args x := Env.cons (encoding x.1) (@Input.args β tail x.2)
  representation := ArgumentRepresentation.cons
    (Representation.ofEmbedding encoding) (@Input.representation β tail)
  represented x := ⟨rfl, @Input.represented β tail x.2⟩

/-- Register a lossless mathematical presentation of an existing input layout.
The embedding commonly exposes structure fields. This is not compilation of an
arbitrary host transformation, and introduces no uncharged runtime operation. -/
def comap {α : Type u} {β : Type v} (input : Input α) (view : β ↪ α) : Input β where
  params := @Input.params α input
  heap x := @Input.heap α input (view x)
  args x := @Input.args α input (view x)
  representation := {
    Rel x args heap := (@Input.representation α input).Rel (view x) args heap
    functional first second :=
      view.injective ((@Input.representation α input).functional first second) }
  represented x := @Input.represented α input (view x)

/-- One ordinary natural argument, with no initial source objects. -/
instance nat : Input Nat := ofEmbedding (τ := .nat) (Function.Embedding.refl Nat)

/-- One ordinary Boolean argument, with no initial source objects. -/
instance bool : Input Bool := ofEmbedding (τ := .bool) (Function.Embedding.refl Bool)

/-- One unit argument, with no initial source objects. -/
instance unit : Input Unit := ofEmbedding (τ := .unit) (Function.Embedding.refl Unit)

/-- One initially populated natural-array object, using the existing canonical
buffer view and argument environment. Input loading is outside execution. -/
instance arrayNat : Input (Array Nat) where
  params := [.buffer .nat]
  heap := ArrayFunction.inputHeap
  args := ArrayFunction.inputArgs
  representation := ArgumentRepresentation.single (Representation.array .nat)
  represented := ArrayFunction.inputBuffer_contents

/-- A natural prefix is a separate parameter, leaving the remaining input's
initial objects unchanged. Iteration supports multiple right-associated fields. -/
instance natProd {β : Type v} [Input β] : Input (Nat × β) :=
  consScalar (τ := .nat) (Function.Embedding.refl Nat) inferInstance

/-- A Boolean prefix is a separate parameter over the remaining input heap. -/
instance boolProd {β : Type v} [Input β] : Input (Bool × β) :=
  consScalar (τ := .bool) (Function.Embedding.refl Bool) inferInstance

/-- A unit prefix is a separate parameter over the remaining input heap. -/
instance unitProd {β : Type v} [Input β] : Input (Unit × β) :=
  consScalar (τ := .unit) (Function.Embedding.refl Unit) inferInstance

end Input

namespace Output

/-- Observe an ordinary natural return value. -/
instance nat : Output Nat where
  type := .nat
  representation := Representation.nat

/-- Observe an ordinary Boolean return value. -/
instance bool : Output Bool where
  type := .bool
  representation := Representation.bool

/-- Observe an ordinary unit return value. -/
instance unit : Output Unit where
  type := .unit
  representation := Representation.unit

/-- Observe the actual returned buffer's natural-array contents at the final heap. -/
instance arrayNat : Output (Array Nat) where
  type := .buffer .nat
  representation := Representation.array .nat

/-- Observe both fields of an actual product result at the same final heap. -/
instance prod {α : Type u} {β : Type v} [Output α] [Output β] : Output (α × β) where
  type := .prod (Output.type α) (Output.type β)
  representation := Representation.prod
    (Output.representation (β := α)) (Output.representation (β := β))

/-- Observe the actual optional payload; an absent result has no default contents. -/
instance option {α : Type u} [Output α] : Output (Option α) where
  type := .option (Output.type α)
  representation := Representation.option (Output.representation (β := α))

end Output

end Complexity.Program
