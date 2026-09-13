/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Range.Represented
import Complexity.Language.Eval.Verification
import Complexity.Language.Linking.Verification
import Complexity.Language.Verification.Heap

/-!
# Finite range folds with an actual source callback

The runtime maintains a cursor and an arbitrarily represented accumulator in
source locals. Each round calls the selected source function, assigns its actual
result, and advances the cursor. No runtime list of indices is constructed.

`body_total` reuses the existing heap-indexed finite-range correspondence. Its
mathematical result is ordinary `List.range'` and `List.foldl`, and its frame is
supplied by the callback at each actual intermediate heap. Heap-shape extension
alone does not preserve mutable array contents. None of these correctness rules
depends on a resource budget.
-/

namespace Complexity.Language.Range.Fold

variable {signatures : List Signature} {accTy : Ty} {α : Type}

/-- A range step receives the current mathematical index and actual accumulator. -/
def stepSignature (accTy : Ty) : Signature :=
  ⟨[.nat, accTy], accTy⟩

/-- Bounds and stride are frozen before the actual loop starts. -/
def foldSignature (accTy : Ty) : Signature :=
  ⟨[.nat, .nat, .nat, accTy], accTy⟩

/-- Actual input operands, without constructing a runtime range collection. -/
def args (start stop stride : Nat) (initial : Value accTy) :
    Env (foldSignature accTy).params :=
  Env.cons start (Env.cons stop (Env.cons stride (Env.cons initial Env.empty)))

/-- The selected source step's real arguments. -/
def calleeArgs (index : Nat) (acc : Value accTy) : Env (stepSignature accTy).params :=
  Env.cons index (Env.cons acc Env.empty)

/-- Whole-signature transport of the existing source evaluation. -/
noncomputable def calleeEval (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy) (index : Nat) (acc : Value accTy) :
    ExceptT Fault (StateT Heap Part) (Value accTy) :=
  (cast (congrArg (fun signature => Env signature.params →
    ExceptT Fault (StateT Heap Part) (Value signature.result)) same)
    (source.eval fn)) (calleeArgs index acc)

/-- Budget-free callback correspondence at arbitrary actual intermediate heaps.
The supplied frame can be weak (`True`) or a proved contents-preservation relation. -/
def Contract (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy) (R : Representation α accTy)
    (step : Nat → α → α) (frame : Heap → Heap → Prop) : Prop :=
  ∀ index initial acc heap, R.Rel initial acc heap → ∃ value finish,
    calleeEval source fn same index acc heap = Part.some (.ok value, finish) ∧
    R.Rel (step index initial) value finish ∧ frame heap finish

/-- The real loop-local order is accumulator, cursor, then the frozen arguments. -/
def loopContext (accTy : Ty) : List Ty :=
  accTy :: .nat :: (foldSignature accTy).params

/-- Full source locals, retaining the untouched bound and initial-input slots. -/
def loopEnv (index : Nat) (acc : Value accTy) (start stop stride : Nat)
    (initial : Value accTy) : Env (loopContext accTy) :=
  Env.cons acc (Env.cons index (args start stop stride initial))

/-- The actual guard computes the cursor comparison in the source language. -/
def guard (accTy : Ty) : Stmt signatures (loopContext accTy) .bool :=
  .letPrim (.lt (.var (.there .here)) (.var (.there (.there (.there .here)))))
    (.ret (.var .here))

/-- One real callback, its accumulator assignment, and the real cursor increment. -/
def iteration (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy) :
    Stmt signatures (loopContext accTy) accTy :=
  Stmt.callOfEq fn same
    (.cons (.var (.there .here)) (.cons (.var .here) .nil))
    (.seq (.assign (.there .here) (.atom (.var .here)))
      (.assign (.there (.there .here))
        (.add (.var (.there (.there .here)))
          (.var (.there (.there (.there (.there (.there .here)))))))))

/-- A single source while; iteration is not recursion of the fold entry. -/
def loop (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy) :
    Stmt signatures (loopContext accTy) accTy :=
  .while (guard accTy) (iteration fn same)

/-- Initialize cursor and accumulator locals, run the range, then return the
actual final accumulator. Both initial copies belong to the source program. -/
def body (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy) :
    Stmt signatures (foldSignature accTy).params accTy :=
  .letPrim (.atom (.var .here))
    (.letPrim (.atom (.var (.there (.there (.there (.there .here))))))
      (.seq (loop fn same) (.ret (.var .here))))

/-- Expose the callback's existing total source contract at ordinary mathematical
arguments, retaining its supplied frame at its actual final heap. -/
theorem Contract.total {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame) (index : Nat) (initial : α) :
    FunctionTotal source fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm)
        (fun actual heap => actual.head = index ∧ R.Rel initial actual.tail.head heap))
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm)
        (fun _ heap value finish => R.Rel (step index initial) value finish ∧
          frame heap finish)) := by
  apply (FunctionTotal.cast_iff_eval source fn same _ _).mpr
  refine (Env.forall_cons (τ := .nat) (Γ := [accTy]) _).mpr ?_
  intro actualIndex
  refine (Env.forall_cons (τ := accTy) (Γ := []) _).mpr ?_
  intro acc
  refine (Env.forall_nil _).mpr ?_
  intro heap represented
  change actualIndex = index ∧ R.Rel initial acc heap at represented
  rcases represented with ⟨sameIndex, observed⟩
  subst actualIndex
  exact callee index initial acc heap observed

/-- The guard preserves the complete current heap and lexical environment. -/
theorem guard_exec (source : Program signatures) (index : Nat) (acc : Value accTy)
    (start stop stride : Nat) (initial : Value accTy) (heap : Heap) :
    Exec source (guard accTy)
      ⟨loopEnv index acc start stop stride initial, heap⟩
      ⟨loopEnv index acc start stop stride initial, heap⟩
      (.returned (decide (index < stop))) :=
  .letPrim (.ret (.var .here) _)

/-- One complete iteration has its actual returned accumulator and final heap;
the callback's frame is not replaced by a heap-shape assumption. -/
theorem iteration_total {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame)
    (index : Nat) (initial : α) (acc : Value accTy)
    (start stop stride : Nat) (original : Value accTy) (heap : Heap)
    (observed : R.Rel initial acc heap) :
    TotalWP source (iteration fn same)
      (fun finish => ∃ value finalHeap,
        finish = ⟨loopEnv (index + stride) value start stop stride original, finalHeap⟩ ∧
        R.Rel (step index initial) value finalHeap ∧ frame heap finalHeap)
      (fun _ _ => False) ⟨loopEnv index acc start stop stride original, heap⟩ := by
  unfold iteration
  apply TotalWP.callOfEq same (callee.total index initial)
  · exact ⟨rfl, observed⟩
  · intro value finalHeap property
    apply (TotalWP.seq_iff _ _).mpr
    apply TotalWP.assign
    apply TotalWP.assign
    exact ⟨value, finalHeap, rfl, property⟩

/-- The existing represented range theorem gives a real finite execution of
this loop. Its frame composes at actual endpoints; its termination is budget-free. -/
theorem loop_total {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame)
    (frameRefl : ∀ heap, frame heap heap)
    (frameTrans : ∀ first second third, frame first second → frame second third →
      frame first third)
    (start stop stride : Nat) (positive : 0 < stride)
    (initial : α) (acc : Value accTy) (heap : Heap)
    (observed : R.Rel initial acc heap) :
    TotalWP source (loop fn same)
      (fun finish => ∃ value,
        finish.locals = loopEnv
          (start + (stop - start + stride - 1) / stride * stride)
          value start stop stride acc ∧
        R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
          (fun state index => step index state) initial) value finish.heap ∧
        frame heap finish.heap)
      (fun _ _ => False) ⟨loopEnv start acc start stop stride acc, heap⟩ := by
  let stateRel (index : Nat) (value : α) (locals : Env (loopContext accTy))
      (current : Heap) : Prop :=
    ∃ actual, locals = loopEnv index actual start stop stride acc ∧
      R.Rel value actual current ∧ frame heap current
  have guardRel : ∀ index value locals current, stateRel index value locals current →
      ∃ after finish,
        Stmt.observe (Equiv.refl _) (guard accTy) source locals current =
          Part.some ((.returned (decide (index < stop)), after), finish) ∧
        stateRel index value after finish := by
    rintro index value locals current ⟨actual, rfl, related, framed⟩
    exact ⟨_, current, Stmt.observe_eq_some_iff.mpr
      (guard_exec source index actual start stop stride acc current),
      actual, rfl, related, framed⟩
  have bodyRel : ∀ index value locals current, index < stop →
      stateRel index value locals current →
      ∃ control after finish,
        Stmt.observe (Equiv.refl _) (iteration fn same) source locals current =
          Part.some ((control, after), finish) ∧
        stateRel (index + stride) (step index value) after finish ∧
        control.Represents R none finish := by
    rintro index value locals current _ ⟨actual, rfl, related, framed⟩
    obtain ⟨finish, control, executed, property⟩ :=
      iteration_total callee index value actual start stop stride acc current related
    cases control with
    | normal =>
        obtain ⟨next, finalHeap, rfl, nextRelated, nextFrame⟩ := property
        exact ⟨.normal, _, finalHeap, Stmt.observe_eq_some_iff.mpr executed,
          ⟨next, rfl, nextRelated, frameTrans heap current finalHeap framed nextFrame⟩,
          trivial⟩
    | returned _ => exact False.elim property
    | fault _ => exact False.elim property
  obtain ⟨control, after, finish, evaluated, outcome⟩ :=
    Stmt.observe_while_rel_forIn_range_step (Equiv.refl _) source
      (guard accTy) (iteration fn same) stop stride positive stateRel R
      (fun index value => (none, step index value)) guardRel
      (by simpa only [Option.isSome_none, Bool.false_eq_true, if_false] using bodyRel)
      start initial (loopEnv start acc start stop stride acc) heap
      ⟨acc, rfl, observed, frameRefl heap⟩
  simp only [Option.elim_none, Stmt.forIn_range_step_yield_eq_foldl, Id.run] at outcome
  have normal : control = .normal := by
    cases control with
    | normal => rfl
    | returned _ => exact False.elim outcome.2
    | fault _ => exact False.elim outcome.2
  subst control
  exact ⟨⟨after, finish⟩, .normal, Stmt.observe_eq_some_iff.mp evaluated, outcome.1⟩

/-- The initialized source body returns the ordinary range fold. The whole
execution additionally supplies heap-shape extension, independently of the frame. -/
theorem body_total {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame)
    (frameRefl : ∀ heap, frame heap heap)
    (frameTrans : ∀ first second third, frame first second → frame second third →
      frame first third)
    (start stop stride : Nat) (positive : 0 < stride)
    (initial : α) (acc : Value accTy) (heap : Heap)
    (observed : R.Rel initial acc heap) :
    TotalWP source (body fn same) (fun _ => False)
      (fun value finish =>
        R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
          (fun state index => step index state) initial) value finish.heap ∧
        frame heap finish.heap ∧ heap.ShapeExtends finish.heap)
      ⟨args start stop stride acc, heap⟩ := by
  have total : TotalWP source (body fn same) (fun _ => False)
      (fun value finish =>
        R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
          (fun state index => step index state) initial) value finish.heap ∧
        frame heap finish.heap) ⟨args start stop stride acc, heap⟩ := by
    unfold body
    apply TotalWP.letPrim
    apply TotalWP.letPrim
    apply (TotalWP.seq_iff _ _).mpr
    apply (loop_total callee frameRefl frameTrans start stop stride positive
      initial acc heap observed).mono_post
    · rintro ⟨locals, finalHeap⟩ ⟨value, rfl, related, framed⟩
      apply (TotalWP.ret_iff _).mpr
      exact ⟨related, framed⟩
    · intro _ _ impossible
      exact False.elim impossible
  obtain ⟨finish, control, executed, property⟩ := total
  refine ⟨finish, control, executed, ?_⟩
  cases control with
  | normal => exact False.elim property
  | returned value => exact ⟨property.1, property.2, executed.heap_shapeExtends⟩
  | fault _ => exact False.elim property

/-- Observe the actual body evaluation, including its complete final source
state, without introducing an alternative interpreter or executable callback. -/
theorem body_eval_exists {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame)
    (frameRefl : ∀ heap, frame heap heap)
    (frameTrans : ∀ first second third, frame first second → frame second third →
      frame first third)
    (start stop stride : Nat) (positive : 0 < stride)
    (initial : α) (acc : Value accTy) (heap : Heap)
    (observed : R.Rel initial acc heap) :
    ∃ value finish,
      (body fn same).action source ⟨args start stop stride acc, heap⟩ =
        Part.some (.returned value, finish) ∧
      R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
        (fun state index => step index state) initial) value finish.heap ∧
      frame heap finish.heap ∧ heap.ShapeExtends finish.heap := by
  obtain ⟨finish, control, executed, property⟩ :=
    body_total callee frameRefl frameTrans start stop stride positive initial acc heap observed
  cases control with
  | normal => exact False.elim property
  | returned value =>
      exact ⟨value, finish, Stmt.action_eq_some_iff.mpr executed, property⟩
  | fault _ => exact False.elim property

/-- A selected function in the same table reuses the fold body directly. This
interface permits the callback and range wrapper to share a source program,
without a cyclic import or a second implementation of the loop. -/
theorem function_eval_exists {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy} {R : Representation α accTy}
    {step : Nat → α → α} {frame : Heap → Heap → Prop}
    (callee : Contract source fn same R step frame)
    (frameRefl : ∀ heap, frame heap heap)
    (frameTrans : ∀ first second third, frame first second → frame second third →
      frame first third)
    (entry : Fin signatures.length) (entrySame : signatures[entry] = foldSignature accTy)
    (selected :
      cast (congrArg (fun signature => Stmt signatures signature.params signature.result)
        entrySame) (source.body entry) = body fn same)
    (start stop stride : Nat) (positive : 0 < stride)
    (initial : α) (acc : Value accTy) (heap : Heap)
    (observed : R.Rel initial acc heap) :
    ∃ value finish,
      (cast (congrArg (fun signature => Env signature.params →
        ExceptT Fault (StateT Heap Part) (Value signature.result)) entrySame)
        (source.eval entry)) (args start stop stride acc) heap =
          Part.some (.ok value, finish) ∧
      R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
        (fun state index => step index state) initial) value finish ∧
      frame heap finish ∧ heap.ShapeExtends finish := by
  let pre : Env (foldSignature accTy).params → Heap → Prop :=
    fun actual current => actual = args start stop stride acc ∧ current = heap
  let post : Env (foldSignature accTy).params → Heap → Value accTy → Heap → Prop :=
    fun _ _ value finish =>
      R.Rel ((List.range' start ((stop - start + stride - 1) / stride) stride).foldl
        (fun state index => step index state) initial) value finish ∧
      frame heap finish ∧ heap.ShapeExtends finish
  have total : FunctionTotal source entry
      (cast (congrArg (fun s => Env s.params → Heap → Prop) entrySame.symm) pre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) entrySame.symm) post) := by
    apply (FunctionTotal.cast_iff source entry entrySame pre post).mpr
    intro actual current represented
    change actual = args start stop stride acc ∧ current = heap at represented
    rcases represented with ⟨sameArgs, sameHeap⟩
    subst actual
    subst current
    rw [selected]
    obtain ⟨finish, control, executed, property⟩ :=
      body_total callee frameRefl frameTrans start stop stride positive initial acc heap observed
    cases control with
    | normal => exact False.elim property
    | returned value => exact ⟨finish, value, executed, property⟩
    | fault _ => exact False.elim property
  exact (FunctionTotal.cast_iff_eval source entry entrySame pre post).mp total
    (args start stop stride acc) heap ⟨rfl, rfl⟩

end Complexity.Language.Range.Fold
