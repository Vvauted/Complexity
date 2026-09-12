/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List
import Complexity.Language.RepresentedFunction
import Complexity.Language.Linking.Verification
import Complexity.Language.Verification.Heap

/-!
# Folding a linked list through an actual source callback

The runtime traverses immutable nodes with the existing source `while`. The
mathematical list is used only in its proof, not as a runtime length counter or
recursive call stack. Accumulators use an arbitrary shared representation, and
callbacks may allocate and change mutable buffers. Existing node observations
survive by the source semantics' heap-shape preservation theorem.
-/

namespace Complexity.Language.List.Fold

universe u

variable {signatures : List Signature} {accTy : Ty} {kind : CellTy} {α : Type u}

/-- The selected callback receives the accumulator and the current node head. -/
def stepSignature (accTy : Ty) (kind : CellTy) : Signature :=
  ⟨[accTy, kind.toTy], accTy⟩

/-- Folding returns the final accumulator and consumes no input node. -/
def foldSignature (accTy : Ty) (kind : CellTy) : Signature :=
  ⟨[accTy, .option (.node kind)], accTy⟩

/-- The actual two-local traversal state. -/
def state (acc : Value accTy) (root : Option (NodeRef kind)) (heap : Heap) :
    State [accTy, .option (.node kind)] :=
  ⟨Env.cons acc (Env.cons root Env.empty), heap⟩

/-- Callback arguments retain the actual represented accumulator. -/
def calleeArgs (acc : Value accTy) (head : CellValue kind) :
    Env (stepSignature accTy kind).params :=
  Env.cons acc (Env.cons (kind.toValue head) Env.empty)

/-- Whole-signature transport of the selected callback's actual source body. -/
def calleeBody (program : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    Stmt signatures (stepSignature accTy kind).params accTy :=
  cast (congrArg (fun signature => Stmt signatures signature.params signature.result)
    same) (program.body fn)

/-- A represented accumulator paired with the actual scalar head. -/
def stepRepresentation (R : Representation α accTy) (kind : CellTy) :
    FunctionRepresentation (α × CellValue kind) (fun _ => α)
      (stepSignature accTy kind) :=
  .ofResult (.cons R (.single (Representation.cell kind))) (fun _ => R)

/-- Mathematical callback correctness on the selected source implementation.
The domain need hold only on accumulators actually reached by the fold. -/
def Contract (program : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind)
    (R : Representation α accTy) (step : α → CellValue kind → α)
    (domain : α → CellValue kind → Prop) : Prop :=
  RepresentedFunction.Refines program fn
    (cast (congrArg (FunctionRepresentation (α × CellValue kind) (fun _ => α))
      same.symm) (stepRepresentation R kind))
    (fun input => domain input.1 input.2) (fun input => step input.1 input.2)

/-- Every actual mathematical prefix supplies an admissible callback input. -/
def Admissible (step : α → CellValue kind → α)
    (domain : α → CellValue kind → Prop) (initial : α)
    (values : List (CellValue kind)) : Prop :=
  ∀ processed head suffix, values = processed ++ head :: suffix →
    domain (processed.foldl step initial) head

/-- The guard observes only whether the current optional node exists. -/
def guard (accTy : Ty) (kind : CellTy) :
    Stmt signatures [accTy, .option (.node kind)] .bool :=
  .matchOption (.var (.there .here)) (.ret (.bool false)) (.ret (.bool true))

/-- Read one actual node, call the selected function, and advance both locals.
The node's tail is captured before the callback and is not read from a buffer. -/
def iteration (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    Stmt signatures [accTy, .option (.node kind)] accTy :=
  .matchOption (.var (.there .here)) .skip
    (.readNode (.var .here)
      (.letPrim (.fst (.var .here))
        (Stmt.callOfEq fn same
          (.cons (.var (.there (.there (.there .here)))) (.cons (.var .here) .nil))
          (.seq
            (.assign (.there (.there (.there (.there .here)))) (.atom (.var .here)))
            (.assign (.there (.there (.there (.there (.there .here)))))
              (.snd (.var (.there (.there .here)))))))))

/-- A real source while loop, with no recursive source invocation of fold. -/
def loop (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    Stmt signatures [accTy, .option (.node kind)] accTy :=
  .while (guard accTy kind) (iteration fn same)

/-- Traverse the shared chain and return the actual final accumulator. -/
def body (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind) :
    Stmt signatures (foldSignature accTy kind).params accTy :=
  .seq (loop fn same) (.ret (.var .here))

@[simp] theorem admissible_nil (step : α → CellValue kind → α)
    (domain : α → CellValue kind → Prop) (initial : α) :
    Admissible step domain initial [] := by
  intro processed head suffix equality
  have lengths := congrArg List.length equality
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

/-- The callback domain is checked at exactly the accumulator passed at each step. -/
theorem admissible_cons (step : α → CellValue kind → α)
    (domain : α → CellValue kind → Prop) (initial : α)
    (head : CellValue kind) (rest : List (CellValue kind)) :
    Admissible step domain initial (head :: rest) ↔
      domain initial head ∧ Admissible step domain (step initial head) rest := by
  constructor
  · intro allowed
    refine ⟨allowed [] head rest rfl, ?_⟩
    intro processed value suffix equality
    exact allowed (head :: processed) value suffix (by simp only [List.cons_append, equality])
  · rintro ⟨first, remaining⟩ processed value suffix equality
    cases processed with
    | nil =>
        have selected := List.cons.inj equality
        simpa only [List.foldl_nil, selected.1] using first
    | cons before processed =>
        rcases List.cons.inj equality with ⟨rfl, tailEq⟩
        exact remaining processed value suffix tailEq

/-- Strengthen the actual callback contract by the heap fact supplied by source
execution itself, without restricting effects on mutable buffers. -/
theorem Contract.total {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract program fn same R step domain)
    (initial : α) (head : CellValue kind) (allowed : domain initial head) :
    FunctionTotal program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm)
        (fun args heap => R.Rel initial args.head heap ∧
          (Representation.cell kind).Rel head args.tail.head heap))
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm)
        (fun _ initialHeap value finish =>
          R.Rel (step initial head) value finish ∧ initialHeap.ShapeExtends finish)) := by
  have correct := (RepresentedFunction.Refines.cast_iff program fn same.symm
    (stepRepresentation R kind) (fun input => domain input.1 input.2)
    (fun input => step input.1 input.2)).mp callee (initial, head) allowed
  apply (FunctionTotal.cast_iff program fn same _ _).mpr
  intro args heap input
  obtain ⟨finish, value, execution, related⟩ :=
    (FunctionTotal.cast_iff program fn same _ _).mp correct args heap input
  exact ⟨finish, value, execution, related, execution.heap_shapeExtends⟩

/-- Expose the same actual callback invocation for source and resource proofs. -/
theorem Contract.invocation {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract program fn same R step domain)
    (initial : α) (acc : Value accTy) (head : CellValue kind) (heap : Heap)
    (allowed : domain initial head) (observed : R.Rel initial acc heap) :
    ∃ finish value,
      Exec program (calleeBody program fn same) ⟨calleeArgs acc head, heap⟩
        finish (.returned value) ∧
      R.Rel (step initial head) value finish.heap ∧ heap.ShapeExtends finish.heap := by
  exact (FunctionTotal.cast_iff program fn same _ _).mp
    (callee.total initial head allowed) (calleeArgs acc head) heap
    ⟨observed, by simp [calleeArgs]⟩

/-- One real iteration preserves the captured tail while accepting the callback's
actual final heap and arbitrary represented return value. -/
theorem iteration_total {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract program fn same R step domain)
    (initial : α) (acc : Value accTy) (ref : NodeRef kind)
    (head : CellValue kind) (tail : Option (NodeRef kind)) (heap : Heap)
    (allowed : domain initial head) (observed : R.Rel initial acc heap)
    (found : heap.node? kind ref.object = some (head, tail)) :
    TotalWP program (iteration fn same)
      (fun finish => ∃ value finalHeap, finish = state value tail finalHeap ∧
        R.Rel (step initial head) value finalHeap ∧ heap.ShapeExtends finalHeap)
      (fun _ _ => False) (state acc (some ref) heap) := by
  unfold iteration
  apply TotalWP.matchSome rfl
  apply TotalWP.readNode found
  apply TotalWP.letPrim
  apply TotalWP.callOfEq same (callee.total initial head allowed)
  · exact ⟨observed, by simp [Args.eval, state, State.cons, Env.head, Env.get, Env.cons]⟩
  · intro value finalHeap property
    apply (TotalWP.seq_iff _ _).mpr
    apply TotalWP.assign
    apply TotalWP.assign
    exact ⟨value, finalHeap, rfl, property⟩

/-- Termination and the mathematical fold follow the finite observed chain.
The induction is solely a proof; the source term remains one while loop. -/
theorem loop_total {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract program fn same R step domain)
    (initial : α) (values : List (CellValue kind)) (acc : Value accTy)
    (root : Option (NodeRef kind)) (heap : Heap)
    (allowed : Admissible step domain initial values)
    (accObserved : R.Rel initial acc heap)
    (listObserved : (Representation.list kind).Rel values root heap) :
    TotalWP program (loop fn same)
      (fun finish => ∃ value finalHeap, finish = state value none finalHeap ∧
        R.Rel (values.foldl step initial) value finalHeap ∧ heap.ShapeExtends finalHeap)
      (fun _ _ => False) (state acc root heap) := by
  induction values generalizing initial acc root heap with
  | nil =>
      cases listObserved
      apply (TotalWP.while_iff _ _).mpr
      simp only [guard, TotalWP.matchOption_iff, Atom.eval, state, Env.cons_there,
        Env.cons_here, TotalWP.ret_iff, Bool.false_eq_true, ↓reduceIte]
      exact ⟨acc, heap, rfl, accObserved, Heap.ShapeExtends.refl heap⟩
  | cons head rest ih =>
      obtain ⟨headAllowed, restAllowed⟩ :=
        (admissible_cons step domain initial head rest).mp allowed
      cases listObserved with
      | cons found contents =>
          apply (TotalWP.while_iff _ _).mpr
          simp only [guard, TotalWP.matchOption_iff, Atom.eval, state,
            Env.cons_there, Env.cons_here, TotalWP.ret_iff, State.tail_cons, ↓reduceIte]
          apply (iteration_total callee initial acc _ head _ heap headAllowed
            accObserved found).mono_post
          · rintro finish ⟨value, finalHeap, rfl, related, preserved⟩
            apply (ih (step initial head) value _ finalHeap restAllowed related
              (contents.mono preserved)).mono_post
            · rintro last ⟨result, resultHeap, rfl, resultRelated, resultPreserved⟩
              exact ⟨result, resultHeap, rfl, resultRelated, preserved.trans resultPreserved⟩
            · intro _ _ impossible
              exact impossible
          · intro _ _ impossible
            exact impossible

/-- The actual traversal returns ordinary `List.foldl`, retains the original
shared list, and preserves all old object shapes. No resource budget is assumed. -/
theorem body_total {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract program fn same R step domain)
    (initial : α) (values : List (CellValue kind)) (acc : Value accTy)
    (root : Option (NodeRef kind)) (heap : Heap)
    (allowed : Admissible step domain initial values)
    (accObserved : R.Rel initial acc heap)
    (listObserved : (Representation.list kind).Rel values root heap) :
    TotalWP program (body fn same) (fun _ => False)
      (fun value finish => R.Rel (values.foldl step initial) value finish.heap ∧
        (Representation.list kind).Rel values root finish.heap ∧
        heap.ShapeExtends finish.heap) (state acc root heap) := by
  apply (TotalWP.seq_iff _ _).mpr
  apply (loop_total callee initial values acc root heap allowed accObserved listObserved).mono_post
  · rintro finish ⟨value, finalHeap, rfl, related, preserved⟩
    apply (TotalWP.ret_iff _).mpr
    exact ⟨related, Representation.list_mono listObserved preserved, preserved⟩
  · intro _ _ impossible
    exact False.elim impossible

end Complexity.Language.List.Fold
