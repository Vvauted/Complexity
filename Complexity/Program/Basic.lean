/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.RepresentedFunction

/-!
# Programs with fixed mathematical input and output types

`Complexity.Program α β` selects an existing typed source function. Its input
and output conventions are fixed external instances, not fields chosen by the
candidate program. Registering these conventions is part of the trusted
mathematical interface: they describe preloaded arguments and an observation
of the actual returned value, not free executable transformations.

`Program.Returns` uses the existing source evaluator and the actual final heap.
`Program.Correct` states successful termination and a mathematical relation
without word ranges, storage capacity or a proposed time bound. Input loading
and any later copying or conversion require their own executable implementation
and accounting; selecting a preloaded invocation does not establish heap
independence or persistent ownership of returned mutable storage.
-/

namespace Complexity

universe u v

namespace Program

/-- A fixed preloaded-input convention. Every mathematical input is represented
by its supplied arguments and heap; an empty relation cannot make all calls
vacuous. Registration is part of the mathematical interface, not a candidate
program field or a runtime preprocessing operation. -/
class Input (α : Type u) where
  params : List Language.Ty
  heap : α → Language.Heap
  args : (x : α) → Language.Env params
  representation : Language.ArgumentRepresentation α params
  represented : ∀ x, representation.Rel x (args x) (heap x)

/-- A fixed observation of the returned source value at its actual final heap.
Registration chooses the mathematical interface, not an executable decoder or
a specification-dependent transformation supplied by a candidate program. -/
class Output (β : Type v) where
  type : Language.Ty
  representation : Language.Representation β type

end Program

/-- One existing source function with fixed mathematical input and output
conventions. The implementation contains source syntax, never a host evaluator
or a desired mathematical answer. -/
structure Program (α : Type u) (β : Type v) [Program.Input α] [Program.Output β] where
  signatures : List Language.Signature
  source : Language.Program signatures
  fn : Fin signatures.length
  signature : signatures[fn] = ⟨Program.Input.params α, Program.Output.type β⟩

namespace Program

variable {α : Type u} {β : Type v} [Input α] [Output β]

/-- Select a declared function without changing its source body or installing
input or output conversions in the implementation. -/
def ofProgram {signatures : List Language.Signature} (source : Language.Program signatures)
    (fn : Fin signatures.length)
    (signature : signatures[fn] = ⟨Input.params α, Output.type β⟩) : Program α β where
  signatures := signatures
  source := source
  fn := fn
  signature := signature

/-- Transport the fixed input arguments through the selected signature equality. -/
def args (p : Program α β) (x : α) : Language.Env p.signatures[p.fn].params :=
  cast (congrArg Language.Env (congrArg Language.Signature.params p.signature).symm)
    (Input.args x)

/-- The fixed input observation at the selected source signature. -/
def inputRepresentation (p : Program α β) :
    Language.ArgumentRepresentation α p.signatures[p.fn].params :=
  cast (congrArg (Language.ArgumentRepresentation α)
    (congrArg Language.Signature.params p.signature).symm) (Input.representation (α := α))

omit [Input α] in
private theorem argumentRepresentation_cast_rel {Γ Δ : List Language.Ty}
    (same : Γ = Δ) (representation : Language.ArgumentRepresentation α Γ)
    (x : α) (args : Language.Env Γ) (heap : Language.Heap) :
    (cast (congrArg (Language.ArgumentRepresentation α) same) representation).Rel x
      (cast (congrArg Language.Env same) args) heap ↔ representation.Rel x args heap := by
  cases same
  rfl

/-- The transported arguments still represent every mathematical input. -/
theorem input_represented (p : Program α β) (x : α) :
    p.inputRepresentation.Rel x (p.args x) (Input.heap x) := by
  exact (argumentRepresentation_cast_rel
    (congrArg Language.Signature.params p.signature).symm
    (Input.representation (α := α)) x (Input.args x) (Input.heap x)).mpr (Input.represented x)

/-- Observe the actual result through the fixed output representation. This
transport changes only its type, not its returned value or final heap. -/
def resultRepresentation (p : Program α β) :
    Language.Representation β p.signatures[p.fn].result :=
  cast (congrArg (Language.Representation β)
    (congrArg Language.Signature.result p.signature).symm) (Output.representation (β := β))

/-- Reuse the existing represented-function contract for this fixed interface. -/
def functionRepresentation (p : Program α β) :
    Language.FunctionRepresentation α (fun _ => β) p.signatures[p.fn] :=
  Language.FunctionRepresentation.ofResult p.inputRepresentation (fun _ => p.resultRepresentation)

/-- Successful evaluation of the selected implementation on the fixed input,
with the mathematical output observed in the actual final heap. -/
def Returns (p : Program α β) (x : α) (y : β) : Prop :=
  ∃ value heap, p.source.eval p.fn (p.args x) (Input.heap x) =
    Part.some (.ok value, heap) ∧ p.resultRepresentation.Rel y value heap

/-- Successful source termination and the required mathematical relation for
every legal input, independently of machine and resource conditions. -/
def Correct (p : Program α β) (valid : α → Prop) (post : α → β → Prop) : Prop :=
  ∀ x, valid x → ∃ y, p.Returns x y ∧ post x y

/-- A return contract describes any actual evaluation of the same invocation,
including its actual final heap, rather than another execution witness. -/
theorem Returns.result_of_eval {p : Program α β} {x : α} {y : β}
    (specified : p.Returns x y)
    {value : Language.Value p.signatures[p.fn].result} {heap : Language.Heap}
    (evaluated : p.source.eval p.fn (p.args x) (Input.heap x) =
      Part.some (.ok value, heap)) : p.resultRepresentation.Rel y value heap := by
  obtain ⟨expectedValue, expectedHeap, expected, represented⟩ := specified
  have same := Part.some_injective (evaluated.symm.trans expected)
  have returned : value = expectedValue := Except.ok.inj (congrArg Prod.fst same)
  have finish : heap = expectedHeap := congrArg Prod.snd same
  simpa only [returned, finish] using represented

/-- The deterministic source evaluation and functional output observation
cannot certify two distinct mathematical results for one input. -/
theorem Returns.unique {p : Program α β} {x : α} {left right : β}
    (first : p.Returns x left) (second : p.Returns x right) : left = right := by
  obtain ⟨value, heap, evaluated, represented⟩ := second
  exact p.resultRepresentation.functional (first.result_of_eval evaluated) represented

/-- Publish an existing source total-correctness contract at the fixed input
boundary. The supplied output observation refers to its actual returned value
and final heap; no separate evaluator or implementation proof is required. -/
theorem Correct.of_functionTotal {p : Program α β} {valid : α → Prop} {post : α → β → Prop}
    {pre : Language.Env p.signatures[p.fn].params → Language.Heap → Prop}
    {result : Language.Env p.signatures[p.fn].params → Language.Heap →
      Language.Value p.signatures[p.fn].result → Language.Heap → Prop}
    (specification : Language.FunctionTotal p.source p.fn pre result)
    (input : ∀ x, valid x → pre (p.args x) (Input.heap x))
    (output : ∀ x, valid x → ∀ value heap,
      result (p.args x) (Input.heap x) value heap →
        ∃ y, p.resultRepresentation.Rel y value heap ∧ post x y) : p.Correct valid post := by
  intro x legal
  obtain ⟨value, heap, evaluated, property⟩ :=
    Language.FunctionTotal.iff_eval.mp specification
      (p.args x) (Input.heap x) (input x legal)
  obtain ⟨y, represented, mathematical⟩ := output x legal value heap property
  exact ⟨y, ⟨value, heap, evaluated, represented⟩, mathematical⟩

/-- Publish a represented source contract on the fixed, inhabited input
convention. The original contract still applies to every actual representation;
this theorem specializes it to the declared preloaded invocation. -/
theorem Correct.of_total {p : Program α β} {valid : α → Prop} {post : α → β → Prop}
    (specification : Language.RepresentedFunction.Total p.source p.fn
      p.functionRepresentation valid post) : p.Correct valid post := by
  intro x legal
  obtain ⟨value, heap, evaluated, y, represented, property⟩ :=
    Language.FunctionTotal.iff_eval.mp (specification x legal)
      (p.args x) (Input.heap x) (p.input_represented x)
  exact ⟨y, ⟨value, heap, evaluated, represented⟩, property⟩

/-- Combine an existing source/native correspondence with ordinary mathematics.
An unrelated mathematical function alone cannot establish this premise. -/
theorem Correct.of_refines {p : Program α β} {valid : α → Prop} {post : α → β → Prop}
    {function : α → β}
    (refinement : Language.RepresentedFunction.Refines p.source p.fn
      p.functionRepresentation valid function)
    (mathematics : ∀ x, valid x → post x (function x)) : p.Correct valid post :=
  Correct.of_total (refinement.of_math mathematics)

end Program

end Complexity
