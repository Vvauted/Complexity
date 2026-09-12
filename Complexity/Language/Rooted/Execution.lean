/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Rooted
import Complexity.Language.Semantics
import Complexity.Language.Heap.Node

/-!
# Object roots through actual source execution

Every finite `Exec` preserves the types and extents of old objects. Scope
cleanup discards only fresh suffix objects, without reverting retained writes.
Faults and missing returns likewise retain preceding effects on old objects.
Rooted initial locals and backward node links produce rooted final locals and
returned values through the same execution, preserving the backward links too.
Reading a node exposes its stored tail, so direct roots alone are insufficient.
Backward links establish object-domain membership, not typed list contents;
neither a second execution relation nor a validity/alias restriction is added.

At calls, the saved caller environment is transported to the callee's actual
final heap before binding the returned value. This separates surviving object
identities from contents, which may change through ordinary writes.
-/

namespace Complexity.Language

/-- Updating a lexical variable retains roots when its new value is rooted. -/
theorem Env.Rooted.set {heap : Heap} {env : Env Γ} (rooted : env.Rooted heap)
    (target : Var Γ τ) (value : Value τ) (valueRooted : ValueRooted heap value) :
    (env.set target value).Rooted heap := by
  induction target with
  | here => exact Env.Rooted.cons (Env.Rooted.tail rooted) value valueRooted
  | there target ih =>
      exact Env.Rooted.cons (ih (Env.Rooted.tail rooted) value valueRooted)
        env.head (Env.Rooted.head rooted)

namespace Exec

/-- Every finite execution preserves existing object identities, types and extents,
including executions that fault after earlier heap effects. -/
theorem heap_shapeExtends {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) :
    Heap.ShapeExtends entry.heap finish.heap := by
  induction execution with
  | skip => exact Heap.ShapeExtends.refl _
  | assign => exact Heap.ShapeExtends.refl _
  | letPrim body ih => exact ih
  | read loaded body ih => exact ih
  | readFault => exact Heap.ShapeExtends.refl _
  | readNode loaded body ih => exact ih
  | readNodeFault => exact Heap.ShapeExtends.refl _
  | write written => exact Heap.shapeExtends_write written
  | writeFault => exact Heap.ShapeExtends.refl _
  | slice sliced body ih => exact ih
  | sliceFault => exact Heap.ShapeExtends.refl _
  | @alloc Γ result kind length initial continuation entry finish control body ih =>
      exact (entry.heap.shapeExtends_alloc (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))).trans ih
  | @consNode Γ result kind head tail continuation entry finish control body ih =>
      exact (entry.heap.shapeExtends_cons (kind.ofValue (head.eval entry.locals))
        (tail.eval entry.locals)).trans ih
  | scope body safe ih => exact ih.take
  | scopeEscape body escapes ih => exact ih
  | seqNormal head tail ihHead ihTail => exact ihHead.trans ihTail
  | seqReturn head ih => exact ih
  | seqFault head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | matchNone selected body ih => exact ih
  | matchSome selected body ih => exact ih
  | whileFalse test ih => exact ih
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact (ihTest.trans ihIteration).trans ihRest
  | whileReturn test iteration ihTest ihIteration => exact ihTest.trans ihIteration
  | whileFault test iteration ihTest ihIteration => exact ihTest.trans ihIteration
  | whileGuardFault test ih => exact ih
  | whileGuardMissingReturn test ih => exact ih
  | ret => exact Heap.ShapeExtends.refl _
  | callReturn callee body ihCallee ihBody => exact ihCallee.trans ihBody
  | callFault callee ih => exact ih
  | callMissingReturn callee ih => exact ih

private theorem node_contents_rooted {heap : Heap} {kind : CellTy} {object : Nat}
    {head : CellValue kind} {tail : Option (NodeRef kind)}
    (backward : Heap.BackwardLinks Heap.nodeReferences heap)
    (loaded : heap.node? kind object = some (head, tail)) :
    ValueRooted heap (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail) := by
  refine ⟨CellTy.toValue_rooted _ _ _, ?_⟩
  cases tail with
  | none => trivial
  | some ref => exact backward.node_tail_lt_size loaded

/-- Actual execution jointly preserves direct roots and backward node links.
The initial link invariant ensures that reading a node cannot expose an absent
tail object; it does not require that the tail denotes a correctly typed list. -/
theorem rooted_backward {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (initialRooted : entry.locals.Rooted entry.heap)
    (initialBackward : Heap.BackwardLinks Heap.nodeReferences entry.heap) :
    finish.locals.Rooted finish.heap ∧ control.Rooted finish.heap ∧
      Heap.BackwardLinks Heap.nodeReferences finish.heap := by
  revert initialRooted initialBackward
  induction execution with
  | skip => exact fun initialRooted initialBackward => ⟨initialRooted, trivial, initialBackward⟩
  | assign target value entry =>
      intro initialRooted initialBackward
      exact ⟨initialRooted.set target _ (value.eval_rooted initialRooted),
        trivial, initialBackward⟩
  | letPrim body ih =>
      intro initialRooted initialBackward
      have finalRooted := ih (Env.Rooted.cons initialRooted _ (Prim.eval_rooted _ initialRooted))
        initialBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | read loaded body ih =>
      intro initialRooted initialBackward
      have finalRooted := ih (Env.Rooted.cons initialRooted _ (CellTy.toValue_rooted _ _ _))
        initialBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | readFault =>
      exact fun initialRooted initialBackward => ⟨initialRooted, trivial, initialBackward⟩
  | readNode loaded body ih =>
      intro initialRooted initialBackward
      have finalRooted := ih
        (Env.Rooted.cons initialRooted _ (node_contents_rooted initialBackward loaded))
        initialBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | readNodeFault =>
      exact fun initialRooted initialBackward => ⟨initialRooted, trivial, initialBackward⟩
  | write written =>
      intro initialRooted initialBackward
      exact ⟨initialRooted.mono (Heap.shapeExtends_write written), trivial,
        initialBackward.write written (fun _ _ => rfl)⟩
  | writeFault =>
      exact fun initialRooted initialBackward => ⟨initialRooted, trivial, initialBackward⟩
  | @slice Γ result kind buffer offset length continuation entry finish control view sliced body ih =>
      intro initialRooted initialBackward
      have bufferRooted : (buffer.eval entry.locals).Rooted entry.heap :=
        buffer.eval_rooted initialRooted
      have viewRooted : view.Rooted entry.heap := Buffer.Rooted.slice bufferRooted sliced
      have finalRooted := ih
        (Env.Rooted.cons (τ := .buffer kind) initialRooted view viewRooted) initialBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | sliceFault =>
      exact fun initialRooted initialBackward => ⟨initialRooted, trivial, initialBackward⟩
  | @alloc Γ result kind length initial continuation entry finish control body ih =>
      intro initialRooted initialBackward
      let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))
      have oldRooted : entry.locals.Rooted allocated.2 :=
        Env.Rooted.mono initialRooted (entry.heap.shapeExtends_alloc
          (length.eval entry.locals) (kind.ofValue (initial.eval entry.locals)))
      have allocatedBackward : Heap.BackwardLinks Heap.nodeReferences allocated.2 :=
        initialBackward.alloc (length.eval entry.locals) (kind.ofValue (initial.eval entry.locals))
          (by simp [Heap.nodeReferences])
      have finalRooted := ih (Env.Rooted.cons (τ := .buffer kind) oldRooted allocated.1
        (entry.heap.alloc_rooted (length.eval entry.locals)
          (kind.ofValue (initial.eval entry.locals)))) allocatedBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | @consNode Γ result kind head tail continuation entry finish control body ih =>
      intro initialRooted initialBackward
      let nodeHead := kind.ofValue (head.eval entry.locals)
      let nodeTail := tail.eval entry.locals
      let allocated := entry.heap.cons nodeHead nodeTail
      have tailRooted : ValueRooted entry.heap (τ := .option (.node kind)) nodeTail :=
        tail.eval_rooted initialRooted
      have oldRooted : entry.locals.Rooted allocated.2 :=
        initialRooted.mono (entry.heap.shapeExtends_cons nodeHead nodeTail)
      have freshRooted : allocated.1.Rooted allocated.2 :=
        Heap.node_lt_size (entry.heap.node?_cons_new nodeHead nodeTail)
      have allocatedBackward : Heap.BackwardLinks Heap.nodeReferences allocated.2 := by
        apply initialBackward.push (.node kind nodeHead nodeTail)
        intro target member
        cases selected : nodeTail with
        | none => simp [selected, Heap.nodeReferences] at member
        | some ref =>
            have same : target = ref.object := by
              simpa only [selected, Heap.nodeReferences, List.mem_singleton] using member
            simp only [selected, ValueRooted, NodeRef.Rooted] at tailRooted
            exact same.symm ▸ (show ref.object < entry.heap.objects.size from tailRooted)
      have finalRooted := ih
        (Env.Rooted.cons (τ := .node kind) oldRooted allocated.1 freshRooted) allocatedBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | @scope Γ result stmt entry finish control body safe ih =>
      intro initialRooted initialBackward
      have retainedShape : entry.heap.ShapeExtends (finish.heap.take entry.heap.objects.size) :=
        body.heap_shapeExtends.take
      have finalBackward := (ih initialRooted initialBackward).2.2
      refine ⟨Env.Rooted.mono safe.1 retainedShape, ?_, finalBackward.take _⟩
      cases control with
      | normal => trivial
      | returned value => exact ValueRooted.mono safe.2 retainedShape
      | fault error => trivial
  | @scopeEscape Γ result stmt entry finish control body escapes ih =>
      intro initialRooted initialBackward
      have finalRooted := ih initialRooted initialBackward
      refine ⟨finalRooted.1, ?_, finalRooted.2.2⟩
      cases control <;> trivial
  | seqNormal head tail ihHead ihTail =>
      intro initialRooted initialBackward
      have middle := ihHead initialRooted initialBackward
      exact ihTail middle.1 middle.2.2
  | seqReturn head ih => exact ih
  | seqFault head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | matchNone selected body ih => exact ih
  | @matchSome Γ result τ value noneBranch someBranch entry payload finish control
      selected body ih =>
      intro initialRooted initialBackward
      have payloadRooted : ValueRooted entry.heap payload := by
        simpa only [selected, ValueRooted] using value.eval_rooted initialRooted
      have finalRooted := ih (Env.Rooted.cons initialRooted payload payloadRooted) initialBackward
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | whileFalse test ih =>
      intro initialRooted initialBackward
      have finalRooted := ih initialRooted initialBackward
      exact ⟨finalRooted.1, trivial, finalRooted.2.2⟩
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      intro initialRooted initialBackward
      have tested := ihTest initialRooted initialBackward
      have iterated := ihIteration tested.1 tested.2.2
      exact ihRest iterated.1 iterated.2.2
  | whileReturn test iteration ihTest ihIteration =>
      intro initialRooted initialBackward
      have tested := ihTest initialRooted initialBackward
      exact ihIteration tested.1 tested.2.2
  | whileFault test iteration ihTest ihIteration =>
      intro initialRooted initialBackward
      have tested := ihTest initialRooted initialBackward
      exact ihIteration tested.1 tested.2.2
  | whileGuardFault test ih => exact ih
  | whileGuardMissingReturn test ih => exact ih
  | ret value entry =>
      intro initialRooted initialBackward
      exact ⟨initialRooted, value.eval_rooted initialRooted, initialBackward⟩
  | callReturn callee body ihCallee ihBody =>
      intro initialRooted initialBackward
      have calleeRooted := ihCallee (Args.eval_rooted _ initialRooted) initialBackward
      have finalRooted := ihBody
        (Env.Rooted.cons (Env.Rooted.mono initialRooted callee.heap_shapeExtends) _ calleeRooted.2.1)
        calleeRooted.2.2
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | callFault callee ih =>
      intro initialRooted initialBackward
      have calleeRooted := ih (Args.eval_rooted _ initialRooted) initialBackward
      exact ⟨initialRooted.mono callee.heap_shapeExtends, trivial, calleeRooted.2.2⟩
  | callMissingReturn callee ih =>
      intro initialRooted initialBackward
      have calleeRooted := ih (Args.eval_rooted _ initialRooted) initialBackward
      exact ⟨initialRooted.mono callee.heap_shapeExtends, trivial, calleeRooted.2.2⟩

/-- Actual execution retains the roots of final locals and any returned value.
The initial backward-link invariant covers references exposed by node reads. -/
theorem rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (initialRooted : entry.locals.Rooted entry.heap)
    (initialBackward : Heap.BackwardLinks Heap.nodeReferences entry.heap) :
    finish.locals.Rooted finish.heap ∧ control.Rooted finish.heap := by
  have preserved := execution.rooted_backward initialRooted initialBackward
  exact ⟨preserved.1, preserved.2.1⟩

/-- Final lexical bindings remain rooted even when execution exits by return or fault. -/
theorem env_rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (initialRooted : entry.locals.Rooted entry.heap)
    (initialBackward : Heap.BackwardLinks Heap.nodeReferences entry.heap) :
    finish.locals.Rooted finish.heap := (execution.rooted initialRooted initialBackward).1

/-- An actual returned value names only objects present in the actual final heap. -/
theorem returned_rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {value : Value result}
    (execution : Exec program stmt entry finish (.returned value))
    (initialRooted : entry.locals.Rooted entry.heap)
    (initialBackward : Heap.BackwardLinks Heap.nodeReferences entry.heap) :
    ValueRooted finish.heap value := (execution.rooted initialRooted initialBackward).2

end Exec

end Complexity.Language
