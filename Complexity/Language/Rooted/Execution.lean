/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Rooted
import Complexity.Language.Semantics

/-!
# Object roots through actual source execution

Every finite `Exec` preserves the types and extents of old objects. Its final
heap is retained on faults and missing returns as well as successful returns.
Rooted initial locals produce rooted final locals and returned values through
the same execution, without a second relation or a validity/alias restriction.

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

/-- Only a returned control outcome carries an object root of its own. -/
@[simp] def Control.Rooted {result : Ty} (control : Control result) (heap : Heap) : Prop :=
  match control with
  | .normal | .fault _ => True
  | .returned value => ValueRooted heap value

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
  | write written => exact Heap.shapeExtends_write written
  | writeFault => exact Heap.ShapeExtends.refl _
  | slice sliced body ih => exact ih
  | sliceFault => exact Heap.ShapeExtends.refl _
  | @alloc Γ result kind length initial continuation entry finish control body ih =>
      exact (entry.heap.shapeExtends_alloc (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))).trans ih
  | seqNormal head tail ihHead ihTail => exact ihHead.trans ihTail
  | seqReturn head ih => exact ih
  | seqFault head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
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

/-- Actual execution retains the roots of final locals and any returned value.
Fault outcomes carry no value, but their final locals still refer to existing objects. -/
theorem rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (initialRooted : entry.locals.Rooted entry.heap) :
    finish.locals.Rooted finish.heap ∧ control.Rooted finish.heap := by
  revert initialRooted
  induction execution with
  | skip => exact fun initialRooted => ⟨initialRooted, trivial⟩
  | assign target value entry =>
      intro initialRooted
      exact ⟨initialRooted.set target _ (value.eval_rooted initialRooted), trivial⟩
  | letPrim body ih =>
      intro initialRooted
      have finalRooted := ih (Env.Rooted.cons initialRooted _ (Prim.eval_rooted _ initialRooted))
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | read loaded body ih =>
      intro initialRooted
      have finalRooted := ih (Env.Rooted.cons initialRooted _ (CellTy.toValue_rooted _ _ _))
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | readFault => exact fun initialRooted => ⟨initialRooted, trivial⟩
  | write written =>
      intro initialRooted
      exact ⟨initialRooted.mono (Heap.shapeExtends_write written), trivial⟩
  | writeFault => exact fun initialRooted => ⟨initialRooted, trivial⟩
  | @slice Γ result kind buffer offset length continuation entry finish control view sliced body ih =>
      intro initialRooted
      have bufferRooted : (buffer.eval entry.locals).Rooted entry.heap :=
        buffer.eval_rooted initialRooted
      have viewRooted : view.Rooted entry.heap := Buffer.Rooted.slice bufferRooted sliced
      have finalRooted := ih
        (Env.Rooted.cons (τ := .buffer kind) initialRooted view viewRooted)
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | sliceFault => exact fun initialRooted => ⟨initialRooted, trivial⟩
  | @alloc Γ result kind length initial continuation entry finish control body ih =>
      intro initialRooted
      let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))
      have oldRooted : entry.locals.Rooted allocated.2 :=
        Env.Rooted.mono initialRooted (entry.heap.shapeExtends_alloc
          (length.eval entry.locals) (kind.ofValue (initial.eval entry.locals)))
      have finalRooted := ih (Env.Rooted.cons (τ := .buffer kind) oldRooted allocated.1
        (entry.heap.alloc_rooted (length.eval entry.locals)
          (kind.ofValue (initial.eval entry.locals))))
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | seqNormal head tail ihHead ihTail =>
      intro initialRooted
      exact ihTail (ihHead initialRooted).1
  | seqReturn head ih => exact ih
  | seqFault head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | whileFalse test ih =>
      intro initialRooted
      exact ⟨(ih initialRooted).1, trivial⟩
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      intro initialRooted
      exact ihRest (ihIteration (ihTest initialRooted).1).1
  | whileReturn test iteration ihTest ihIteration =>
      intro initialRooted
      exact ihIteration (ihTest initialRooted).1
  | whileFault test iteration ihTest ihIteration =>
      intro initialRooted
      exact ihIteration (ihTest initialRooted).1
  | whileGuardFault test ih => exact ih
  | whileGuardMissingReturn test ih => exact ih
  | ret value entry =>
      intro initialRooted
      exact ⟨initialRooted, value.eval_rooted initialRooted⟩
  | callReturn callee body ihCallee ihBody =>
      intro initialRooted
      have calleeRooted := ihCallee (Args.eval_rooted _ initialRooted)
      have finalRooted := ihBody
        (Env.Rooted.cons (Env.Rooted.mono initialRooted callee.heap_shapeExtends) _ calleeRooted.2)
      exact ⟨Env.Rooted.tail finalRooted.1, finalRooted.2⟩
  | callFault callee ih =>
      intro initialRooted
      exact ⟨initialRooted.mono callee.heap_shapeExtends, trivial⟩
  | callMissingReturn callee ih =>
      intro initialRooted
      exact ⟨initialRooted.mono callee.heap_shapeExtends, trivial⟩

/-- Final lexical bindings remain rooted even when execution exits by return or fault. -/
theorem env_rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (initialRooted : entry.locals.Rooted entry.heap) :
    finish.locals.Rooted finish.heap := (execution.rooted initialRooted).1

/-- An actual returned value names only objects present in the actual final heap. -/
theorem returned_rooted {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {value : Value result}
    (execution : Exec program stmt entry finish (.returned value))
    (initialRooted : entry.locals.Rooted entry.heap) :
    ValueRooted finish.heap value := (execution.rooted initialRooted).2

end Exec

end Complexity.Language
