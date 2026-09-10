/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Semantics
import Complexity.Language.Heap.Prefix

/-!
# Preserving existing objects through allocation-only heap effects

`Stmt.NoCellWrites` excludes explicit source cell updates while allowing fresh
allocation and initialization. This is not a claim that the generated RAM code
performs no memory writes. It is a conservative source effect condition: even
an explicit update of a newly allocated object is excluded.

`Exec.heap_prefix` retains every original object, including its exact contents,
through the existing finite source execution. A call's syntactic condition
checks its continuation; the theorem separately requires the same condition
for every function body, including recursive callees. Guards and faulting
callees retain their actual heap effects instead of rolling back allocations.
Safe scope exits may discard their fresh suffix; all entry objects still retain
their exact contents. Escaping scope exits retain the complete current heap.
-/

namespace Complexity.Language

namespace Stmt

/-- No explicit cell update occurs in this statement's own syntax. Calls check
only their continuation; execution framing additionally checks all callee bodies. -/
@[simp] def NoCellWrites {signatures : List Signature} {Γ : List Ty} {result : Ty} :
    Stmt signatures Γ result → Prop
  | .skip | .assign .. | .ret _ => True
  | .letPrim _ continuation => continuation.NoCellWrites
  | .read _ _ continuation => continuation.NoCellWrites
  | .write .. => False
  | .slice _ _ _ continuation => continuation.NoCellWrites
  | .alloc _ _ continuation => continuation.NoCellWrites
  | .scope body => body.NoCellWrites
  | .call _ _ continuation => continuation.NoCellWrites
  | .seq first second => first.NoCellWrites ∧ second.NoCellWrites
  | .ite _ yes no => yes.NoCellWrites ∧ no.NoCellWrites
  | .while guard body => guard.NoCellWrites ∧ body.NoCellWrites

end Stmt

namespace Exec

/-- Without explicit cell updates in the statement or any callee, all original
objects form an exact prefix of the actual final heap. This includes returns,
faults and missing returns after earlier successful allocations. -/
theorem heap_prefix {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (callees : ∀ fn, (program.body fn).NoCellWrites)
    (unchanged : stmt.NoCellWrites) :
    List.IsPrefix entry.heap.objects.toList finish.heap.objects.toList := by
  revert unchanged
  induction execution with
  | skip => intro _; exact List.prefix_refl _
  | assign => intro _; exact List.prefix_refl _
  | letPrim body ih => intro unchanged; exact ih unchanged
  | read loaded body ih => intro unchanged; exact ih unchanged
  | readFault => intro _; exact List.prefix_refl _
  | write => intro impossible; exact False.elim impossible
  | writeFault => intro impossible; exact False.elim impossible
  | slice sliced body ih => intro unchanged; exact ih unchanged
  | sliceFault => intro _; exact List.prefix_refl _
  | @alloc Γ result kind length initial continuation entry finish control body ih =>
      intro unchanged
      exact (entry.heap.objects_prefix_alloc (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))).trans (ih unchanged)
  | @scope Γ result stmt entry finish control body safe ih =>
      intro unchanged
      change List.IsPrefix entry.heap.objects.toList
        (finish.heap.take entry.heap.objects.size).objects.toList
      rw [Heap.take_eq_of_prefix (ih unchanged)]
      exact List.prefix_refl _
  | scopeEscape body escapes ih => intro unchanged; exact ih unchanged
  | seqNormal head tail ihHead ihTail =>
      intro unchanged
      exact (ihHead unchanged.1).trans (ihTail unchanged.2)
  | seqReturn head ih => intro unchanged; exact ih unchanged.1
  | seqFault head ih => intro unchanged; exact ih unchanged.1
  | iteTrue test body ih => intro unchanged; exact ih unchanged.1
  | iteFalse test body ih => intro unchanged; exact ih unchanged.2
  | whileFalse test ih => intro unchanged; exact ih unchanged.1
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      intro unchanged
      exact ((ihTest unchanged.1).trans (ihIteration unchanged.2)).trans (ihRest unchanged)
  | whileReturn test iteration ihTest ihIteration =>
      intro unchanged
      exact (ihTest unchanged.1).trans (ihIteration unchanged.2)
  | whileFault test iteration ihTest ihIteration =>
      intro unchanged
      exact (ihTest unchanged.1).trans (ihIteration unchanged.2)
  | whileGuardFault test ih => intro unchanged; exact ih unchanged.1
  | whileGuardMissingReturn test ih => intro unchanged; exact ih unchanged.1
  | ret => intro _; exact List.prefix_refl _
  | callReturn callee body ihCallee ihBody =>
      intro unchanged
      exact (ihCallee (callees _)).trans (ihBody unchanged)
  | callFault callee ih => intro _; exact ih (callees _)
  | callMissingReturn callee ih => intro _; exact ih (callees _)

/-- An existing buffer observation survives an entire execution without explicit
cell updates, including allocations in loops and callees. No disjointness among
old views is needed because all their underlying cells are preserved. -/
theorem contents_frame {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control)
    (callees : ∀ fn, (program.body fn).NoCellWrites)
    (unchanged : stmt.NoCellWrites)
    {kind : CellTy} {view : Buffer kind} {contents : Array (CellValue kind)}
    (observed : view.Contents entry.heap contents) :
    view.Contents finish.heap contents :=
  observed.mono_prefix (execution.heap_prefix callees unchanged)

end Exec
end Complexity.Language
