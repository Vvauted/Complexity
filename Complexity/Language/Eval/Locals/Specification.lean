/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals
import Complexity.Control.Triple
import Complexity.Control.Part.StateT

/-!
# Relational contracts for ordinary-local blocks

`Stmt.BlockSpec` packages native total-correctness triples for an existing block
action. Its relations retain the actual initial and final heaps, distinguish
normal completion from return, and reject faults and divergence. Inputs and
outputs may use different ordinary coordinates: a named loop can accept its
mutable variables while returning complete locals, including fixed captures.

The contract introduces no execution semantics. `BlockSpec.spec` applies a
chosen contract in native verification, and `BlockSpec.map_iff` transports its
output coordinates without changing the actual control or heap.
-/

namespace Complexity.Language.Stmt

open scoped Part.TotalCorrectness

/-- Total correctness of an existing block action with relations on ordinary
inputs, actual final locals and both endpoint heaps. Faults are excluded. -/
def BlockSpec {Input Output : Type} {result : Ty}
    (action : Input → StateT Heap Part (Control result × Output))
    (pre : Input → Heap → Prop)
    (normal : Input → Heap → Output → Heap → Prop)
    (returned : Input → Heap → Value result → Output → Heap → Prop) : Prop :=
  ∀ start startHeap, pre start startHeap →
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (action start) (fun heap => ⟨heap = startHeap⟩)
      (fun outcome heap => ⟨match outcome.1 with
        | .normal => normal start startHeap outcome.2 heap
        | .returned value => returned start startHeap value outcome.2 heap
        | .fault _ => False⟩, ⟨⟩)

namespace BlockSpec

variable {Input Output : Type} {result : Ty}
variable {action : Input → StateT Heap Part (Control result × Output)}
variable {pre pre' : Input → Heap → Prop}
variable {normal normal' : Input → Heap → Output → Heap → Prop}
variable {returned returned' : Input → Heap → Value result → Output → Heap → Prop}

/-- Apply a block contract at its actual initial input and heap. -/
theorem «at» (specification : BlockSpec action pre normal returned)
    (start : Input) (startHeap : Heap) (initial : pre start startHeap) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (action start) (fun heap => ⟨heap = startHeap⟩)
      (fun outcome heap => ⟨match outcome.1 with
        | .normal => normal start startHeap outcome.2 heap
        | .returned value => returned start startHeap value outcome.2 heap
        | .fault _ => False⟩, ⟨⟩) :=
  specification start startHeap initial

/-- Recover the mathematical postcondition at an actual finite block result.
The source contract supplies termination and excludes faults; uniqueness of
the same partial computation identifies the observed locals and final heap. -/
theorem post_of_eq (specification : BlockSpec action pre normal returned)
    {start : Input} {startHeap finish : Heap} {control : Control result} {output : Output}
    (initial : pre start startHeap)
    (executed : action start startHeap = Part.some ((control, output), finish)) :
    match control with
    | .normal => normal start startHeap output finish
    | .returned value => returned start startHeap value output finish
    | .fault _ => False := by
  cases control <;>
    exact Part.TotalCorrectness.stateT_post_of_eq
      (specification.«at» start startHeap initial) rfl executed

/-- Strengthen the initial condition and weaken either successful relation.
The consequences may use the condition at the original input and heap; no
preservation of that condition at the final heap is assumed. -/
theorem mono (specification : BlockSpec action pre normal returned)
    (precondition : ∀ start heap, pre' start heap → pre start heap)
    (normalPost : ∀ start heap output finish,
      pre' start heap → normal start heap output finish → normal' start heap output finish)
    (returnedPost : ∀ start heap value output finish,
      pre' start heap → returned start heap value output finish →
        returned' start heap value output finish) :
    BlockSpec action pre' normal' returned' := by
  intro start startHeap initial
  refine (specification.«at» start startHeap (precondition start startHeap initial)).mono
    (fun _ same => same) ?_
  constructor
  · rintro ⟨control, output⟩ finish property
    cases control with
    | normal => exact normalPost start startHeap output finish initial property
    | returned value => exact returnedPost start startHeap value output finish initial property
    | fault error => exact property
  · trivial

/-- Use a chosen block contract with a native continuation postcondition.
The verification condition keeps both branch consequences at the actual entry
heap. This rule does not select or search for a contract automatically. -/
theorem spec (specification : BlockSpec action pre normal returned)
    (start : Input) (post : Std.Do.PostCond (Control result × Output) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (action start)
      (fun heap => ⟨pre start heap ∧
        (∀ output finish, normal start heap output finish →
          (post.1 (.normal, output) finish).down) ∧
        (∀ value output finish, returned start heap value output finish →
          (post.1 (.returned value, output) finish).down)⟩)
      post := by
  apply (Part.TotalCorrectness.stateT_triple_iff _ _ _).mpr
  rintro heap ⟨initial, normalPost, returnedPost⟩
  obtain ⟨⟨control, output⟩, finish, executed, property⟩ :=
    (Part.TotalCorrectness.stateT_triple_iff _ _ _).mp
      (specification.«at» start heap initial) heap rfl
  refine ⟨(control, output), finish, executed, ?_⟩
  cases control with
  | normal => exact normalPost output finish property
  | returned value => exact returnedPost value output finish property
  | fault error => exact False.elim property

/-- Prove a block contract from actual result equations. This reuses native
finite-state adequacy; the supplied outcome is not used to define an evaluator. -/
theorem of_eq (outcome : Input → Heap → (Control result × Output) × Heap)
    (executed : ∀ start heap, pre start heap →
      action start heap = Part.some (outcome start heap))
    (property : ∀ start heap, pre start heap →
      match (outcome start heap).1.1 with
      | .normal => normal start heap (outcome start heap).1.2 (outcome start heap).2
      | .returned value =>
          returned start heap value (outcome start heap).1.2 (outcome start heap).2
      | .fault _ => False) :
    BlockSpec action pre normal returned := by
  intro start heap initial
  exact Part.TotalCorrectness.stateT_triple_of_eq
    (executed start heap initial) (property start heap initial)

/-- Transport an output-local observation through its actual map, preserving
control and the final heap. The map need not be injective: the right-hand
contract asks exactly the properties visible through the mapped coordinates. -/
theorem map_iff {Mapped : Type} (reindex : Output → Mapped)
    (mappedNormal : Input → Heap → Mapped → Heap → Prop)
    (mappedReturned : Input → Heap → Value result → Mapped → Heap → Prop) :
    BlockSpec
      (fun start => (fun outcome => (outcome.1, reindex outcome.2)) <$> action start)
      pre mappedNormal mappedReturned ↔
    BlockSpec action pre
      (fun start heap output finish => mappedNormal start heap (reindex output) finish)
      (fun start heap value output finish =>
        mappedReturned start heap value (reindex output) finish) := by
  simp only [BlockSpec, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp, Functor.map, StateT.map, Bind.bind, Pure.pure,
    Part.bind_some_eq_map]
  constructor
  · intro specification start startHeap initial heap sameHeap
    obtain ⟨⟨⟨control, mapped⟩, finish⟩, member, property⟩ :=
      specification start startHeap initial heap sameHeap
    obtain ⟨⟨⟨actualControl, output⟩, actualFinish⟩, actualMember, same⟩ :=
      (Part.mem_map_iff _).mp member
    cases same
    exact ⟨((actualControl, output), actualFinish), actualMember, property⟩
  · intro specification start startHeap initial heap sameHeap
    obtain ⟨⟨⟨control, output⟩, finish⟩, member, property⟩ :=
      specification start startHeap initial heap sameHeap
    refine ⟨((control, reindex output), finish), ?_, property⟩
    exact (Part.mem_map_iff _).mpr ⟨((control, output), finish), member, rfl⟩

end BlockSpec

end Complexity.Language.Stmt

namespace Complexity.Language

open scoped Part.TotalCorrectness

/-- Use an ordinary block contract as source total correctness at the same
initial locals and heap. The input map may install fixed lexical captures;
both postcondition consequences retain the complete actual output locals and
heap. Faults and divergence remain excluded by the native source contract. -/
theorem TotalWP.of_blockSpec {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Input Locals : Type} (view : Env Γ ≃ Locals) (inputLocals : Input → Locals)
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {pre : Input → Heap → Prop}
    {normalRel : Input → Heap → Locals → Heap → Prop}
    {returnedRel : Input → Heap → Value result → Locals → Heap → Prop}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop}
    (specification : Stmt.BlockSpec
      (fun input => Stmt.observe view stmt program (inputLocals input)) pre normalRel returnedRel)
    {input : Input} {heap : Heap} (initial : pre input heap)
    (normalPost : ∀ output finish, normalRel input heap output finish →
      normal ⟨view.symm output, finish⟩)
    (returnedPost : ∀ value output finish, returnedRel input heap value output finish →
      returned value ⟨view.symm output, finish⟩) :
    TotalWP program stmt normal returned ⟨view.symm (inputLocals input), heap⟩ := by
  apply (TotalWP.iff_triple_observe view (locals := inputLocals input)).mpr
  refine (specification.«at» input heap initial).mono (fun _ same => same) ?_
  constructor
  · rintro ⟨control, output⟩ finish property
    cases control with
    | normal => exact normalPost output finish property
    | returned value => exact returnedPost value output finish property
    | fault error => exact property
  · trivial

end Complexity.Language
