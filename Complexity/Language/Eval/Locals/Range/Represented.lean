/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Range
import Complexity.Language.Representation

/-!
# Finite ranges with heap-indexed mathematical state

The same source `while` can implement a native finite range even when its mutable
state contains represented arrays, lists or records. `stateRel` observes all
relevant locals at the actual heap; it is not an inverse on raw handles. Each
guard and body premise describes an execution of the existing source statement.
Allocation and writes are permitted when those executions establish the stated
mathematical next state. Frames needed by later iterations belong in this same
relation, rather than following from an assumed unchanged heap.

The conclusion retains the actual normal/early-return distinction, final locals
and final heap. Its mathematical result is Lean's existing `forIn` on a positive
finite range. No new evaluator, runtime decoding operation, fuel or cost model is
introduced. Pure scalar correspondence is the equality specialization of these
relations, not a separate condition on the source loop.
-/

namespace Complexity.Language

namespace Control

/-- Relate a native optional early return to the actual source control. Normal
completion has no result, a return observes its value in the final heap, and a
fault cannot establish successful correspondence. -/
def Represents {α : Type} {result : Ty} (control : Control result)
    (representation : Representation α result) (value : Option α) (heap : Heap) : Prop :=
  match control, value with
  | .normal, none => True
  | .returned actual, some expected => representation.Rel expected actual heap
  | _, _ => False

/-- For a pure embedding, relational control correspondence is exactly equality
with the encoded native control. This includes registered scalar records, not
only identity-encoded natural numbers. -/
theorem represents_ofEmbedding_iff {α : Type} {result : Ty}
    (control : Control result) (encoding : α ↪ Value result)
    (value : Option α) (heap : Heap) :
    control.Represents (Representation.ofEmbedding encoding) value heap ↔
      control = value.elim Control.normal (fun result => Control.returned (encoding result)) := by
  cases control <;> cases value <;>
    simp [Represents, Representation.ofEmbedding, eq_comm]

/-- A proved pure result encoding supplies the same relational return fact used
for heap-backed values. The encoding is mathematical transport only. -/
theorem represents_of_embedding {α : Type} {result : Ty}
    (encoding : α ↪ Value result) (value : Option α) (heap : Heap) :
    (value.elim Control.normal (fun result => Control.returned (encoding result))).Represents
      (Representation.ofEmbedding encoding) value heap :=
  (represents_ofEmbedding_iff _ encoding value heap).mpr rfl

/-- Exact native scalar results are a special case of heap-indexed control
correspondence; no value is supplied for ordinary fallthrough. -/
theorem represents_of_eq {result : Ty} (value : Option (Value result)) (heap : Heap) :
    (value.elim Control.normal Control.returned).Represents
      (Representation.ofEmbedding (Function.Embedding.refl (Value result))) value heap :=
  represents_of_embedding (Function.Embedding.refl (Value result)) value heap

end Control

namespace Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {Mutable Locals α : Type}

/-- A finite native range corresponds to the same source `while` through an
arbitrary heap-indexed relation on its complete local state. The guard may have
effects but must retain that mathematical state. The body's actual final heap
represents its native next state; only normal completion advances the cursor.

The relation may retain fixed captures and any required allocation/content
frames. Neither mutable values nor returns need a heap-independent encoding.
Termination comes from the native finite range, independently of RAM resources.
-/
theorem observe_while_rel_forIn_range_step
    (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result)
    (stop stride : Nat) (positive : 0 < stride)
    (stateRel : Nat → Mutable → Locals → Heap → Prop)
    (resultRep : Representation α result)
    (step : Nat → Mutable → Option α × Mutable)
    (guardRel : ∀ index mutable locals heap, stateRel index mutable locals heap →
      ∃ after finish,
        observe view guard program locals heap =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index mutable after finish)
    (bodyRel : ∀ index mutable locals heap, index < stop →
      stateRel index mutable locals heap →
      ∃ control after finish,
        observe view body program locals heap = Part.some ((control, after), finish) ∧
        stateRel (if (step index mutable).1.isSome then index else index + stride)
          (step index mutable).2 after finish ∧
        control.Represents resultRep (step index mutable).1 finish)
    (start : Nat) (mutable : Mutable) (locals : Locals) (heap : Heap)
    (initial : stateRel start mutable locals heap) :
    ∃ control after finish,
      observe view (.while guard body) program locals heap =
        Part.some ((control, after), finish) ∧
      (let outcome := Id.run (forIn (m := Id)
        ({ start := start, stop := stop, step := stride, step_pos := positive } : Std.Legacy.Range)
        ((none, (start, mutable)) : Option α × (Nat × Mutable))
        (fun index state =>
          let iteration := step index state.2.2
          iteration.1.elim
            (pure (ForInStep.yield (none, (index + stride, iteration.2))))
            (fun value => pure (ForInStep.done (some value, (index, iteration.2))))))
       stateRel outcome.2.1 outcome.2.2 after finish ∧
         control.Represents resultRep outcome.1 finish) := by
  let advance (index : Nat) (state : Option α × (Nat × Mutable)) :
      Id (ForInStep (Option α × (Nat × Mutable))) :=
    let iteration := step index state.2.2
    iteration.1.elim
      (pure (.yield (none, (index + stride, iteration.2))))
      (fun value => pure (.done (some value, (index, iteration.2))))
  have finite : ∀ count start mutable locals heap,
      (stop - start + stride - 1) / stride = count →
      stateRel start mutable locals heap →
      ∃ control after finish,
        Exec program (.while guard body) ⟨view.symm locals, heap⟩
          ⟨view.symm after, finish⟩ control ∧
        (let outcome := Id.run (forIn (m := Id) (List.range' start count stride)
          (none, (start, mutable)) advance)
         stateRel outcome.2.1 outcome.2.2 after finish ∧
           control.Represents resultRep outcome.1 finish) := by
    intro count
    induction count with
    | zero =>
        intro start mutable locals heap remaining represented
        have outside : ¬ start < stop := by
          have := (Nat.div_eq_zero_iff_lt positive).mp remaining
          omega
        obtain ⟨after, finish, guarded, retained⟩ :=
          guardRel start mutable locals heap represented
        have executed : Exec program guard ⟨view.symm locals, heap⟩
            ⟨view.symm after, finish⟩ (.returned false) := by
          apply observe_eq_some_iff.mp
          simpa only [outside, decide_false] using guarded
        refine ⟨.normal, after, finish, .whileFalse executed, ?_⟩
        simpa only [List.range'_zero, List.forIn_nil, Id.run, Id.instMonad,
          Control.Represents, and_true] using retained
    | succ count ih =>
        intro start mutable locals heap remaining represented
        have inside : start < stop := by
          by_contra outside
          have empty : (stop - start + stride - 1) / stride = 0 :=
            Nat.div_eq_of_lt (by omega)
          omega
        obtain ⟨afterGuard, guardHeap, guarded, retained⟩ :=
          guardRel start mutable locals heap represented
        have guardExecuted : Exec program guard ⟨view.symm locals, heap⟩
            ⟨view.symm afterGuard, guardHeap⟩ (.returned true) := by
          apply observe_eq_some_iff.mp
          simpa only [inside, decide_true] using guarded
        obtain ⟨control, afterBody, bodyHeap, iterated, nextState, returned⟩ :=
          bodyRel start mutable afterGuard guardHeap inside retained
        have bodyExecuted := observe_eq_some_iff.mp iterated
        cases stepEq : step start mutable with
        | mk optional next =>
            cases optional with
            | none =>
                have normal : control = .normal := by
                  cases control <;>
                    simp_all only [Control.Represents]
                subst control
                have nextRelated : stateRel (start + stride) next afterBody bodyHeap := by
                  simpa only [stepEq, Option.isSome_none, Bool.false_eq_true, if_false] using nextState
                have sizeSucc : (stop - start + stride - 1) / stride =
                    (stop - (start + stride) + stride - 1) / stride + 1 :=
                  Std.Legacy.Range.size_eq_succ_of_start_lt
                    { start := start, stop := stop, step := stride, step_pos := positive } inside
                obtain ⟨control, after, finish, rest, observed⟩ :=
                  ih (start + stride) next afterBody bodyHeap (by omega) nextRelated
                refine ⟨control, after, finish,
                  .whileTrue guardExecuted bodyExecuted rest, ?_⟩
                simpa only [List.range'_succ, List.forIn_cons, advance, stepEq,
                  Id.run, Id.instMonad, Option.elim_none] using observed
            | some value =>
                obtain ⟨actual, actualControl, resultRelated⟩ :
                    ∃ actual, control = .returned actual ∧ resultRep.Rel value actual bodyHeap := by
                  cases control with
                  | normal => simp only [stepEq, Control.Represents] at returned
                  | returned actual =>
                      exact ⟨actual, rfl, by simpa only [stepEq, Control.Represents] using returned⟩
                  | fault error => simp only [Control.Represents] at returned
                subst control
                have nextRelated : stateRel start next afterBody bodyHeap := by
                  simpa only [stepEq, Option.isSome_some, if_true] using nextState
                refine ⟨.returned actual, afterBody, bodyHeap,
                  .whileReturn guardExecuted bodyExecuted, ?_⟩
                simpa only [List.range'_succ, List.forIn_cons, advance, stepEq,
                  Id.run, Id.instMonad, Option.elim_some, Control.Represents] using
                  And.intro nextRelated resultRelated
  obtain ⟨control, after, finish, execution, represented⟩ :=
    finite ((stop - start + stride - 1) / stride) start mutable locals heap rfl initial
  refine ⟨control, after, finish, observe_eq_some_iff.mpr execution, ?_⟩
  simpa only [Std.Legacy.Range.forIn_eq_forIn_range', advance] using represented

end Stmt

end Complexity.Language
