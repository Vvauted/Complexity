/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Program
import Complexity.Language.Eval.Verification

/-!
# Native callback proofs and observations of the same list fold

`Contract.of_pure_eval` reuses a proved pure callback action with any injective
accumulator encoding. Signature transport and source argument environments stay
inside this bridge. Lists remain observations of actual nodes in the current
heap; no encoding or equivalence between a mathematical list and a node handle
is assumed.

`eval_eq_pure_of_contents` derives the exact result and unchanged heap from the
existing fold correctness theorem. It records the initial heap in a ghost
accumulator observation through `Representation.withHeap`; the runtime program,
its accumulator layout, and its callback remain unchanged.
-/

namespace Complexity.Language.List.Fold

open scoped Part.TotalCorrectness

universe u

variable {signatures : List Signature} {accTy : Ty} {kind : CellTy} {α : Type u}

/-- Observe the selected actual callback at its checked step signature. This is
only type transport and argument binding of the existing `Program.eval`. -/
noncomputable def calleeEval (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind)
    (acc : Value accTy) (head : CellValue kind) :
    ExceptT Fault (StateT Heap Part) (Value accTy) :=
  (cast (congrArg (fun signature => Env signature.params →
    ExceptT Fault (StateT Heap Part) (Value signature.result)) same)
    (source.eval fn)) (calleeArgs acc head)

/-- Invoke the actual added fold entry with its represented accumulator and
node handle. The mathematical list is not an executable argument. -/
noncomputable def foldEval (source : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = stepSignature accTy kind)
    (acc : Value accTy) (root : Option (NodeRef kind)) :
    ExceptT Fault (StateT Heap Part) (Value accTy) :=
  (program source fn same).eval (entry accTy kind signatures)
    (Env.cons acc (Env.cons root Env.empty))

/-- A callback's ordinary successful action specification gives the shared
fold contract. Arguments and whole-signature casts are supplied by the bridge. -/
theorem Contract.of_eval {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (evaluated : ∀ initial acc head heap, domain initial head → R.Rel initial acc heap →
      ∃ value finish,
        calleeEval source fn same acc head heap = Part.some (.ok value, finish) ∧
        R.Rel (step initial head) value finish) :
    Contract source fn same R step domain := by
  apply (RepresentedFunction.Refines.cast_iff source fn same.symm
    (stepRepresentation R kind) (fun input => domain input.1 input.2)
    (fun input => step input.1 input.2)).mpr
  rintro ⟨initial, head⟩ allowed
  apply (FunctionTotal.cast_iff_eval source fn same _ _).mpr
  refine (Env.forall_cons (τ := accTy) (Γ := [kind.toTy]) _).mpr ?_
  intro acc
  refine (Env.forall_cons (τ := kind.toTy) (Γ := []) _).mpr ?_
  intro actualHead
  refine (Env.forall_nil _).mpr ?_
  intro heap observed
  change R.Rel initial acc heap ∧ (Representation.cell kind).Rel head actualHead heap at observed
  have headEq : kind.toValue head = actualHead :=
    (Representation.cell_rel kind head actualHead heap).mp observed.2
  subst actualHead
  exact evaluated initial acc head heap allowed observed.1

/-- Reuse an existing pure callback correspondence with any injective native
accumulator encoding. No inverse on invalid runtime values is required. -/
theorem Contract.of_pure_eval {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (encoding : α ↪ Value accTy)
    (correspondence : ∀ initial head, domain initial head →
      calleeEval source fn same (encoding initial) head = pure (encoding (step initial head))) :
    Contract source fn same (Representation.ofEmbedding encoding) step domain := by
  apply Contract.of_eval
  intro initial acc head heap allowed observed
  have encoded : encoding initial = acc := observed
  subst acc
  exact ⟨encoding (step initial head), heap,
    congrFun (correspondence initial head allowed) heap, rfl⟩

/-- The same actual fold action returns its mathematical result and retains
the old list observation, including when callbacks have heap effects. -/
theorem eval_exists {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract source fn same R step domain)
    (initial : α) (values : List (CellValue kind)) (acc : Value accTy)
    (root : Option (NodeRef kind)) (heap : Heap)
    (allowed : Admissible step domain initial values)
    (accObserved : R.Rel initial acc heap)
    (listObserved : (Representation.list kind).Rel values root heap) :
    ∃ value finish,
      foldEval source fn same acc root heap = Part.some (.ok value, finish) ∧
      R.Rel (values.foldl step initial) value finish ∧
      (Representation.list kind).Rel values root finish ∧ heap.ShapeExtends finish :=
  (program_total callee initial values allowed).eval_spec
    (args := Env.cons acc (Env.cons root Env.empty)) (initialHeap := heap)
    ⟨accObserved, listObserved⟩

/-- Compose the actual fold invocation with native continuation proofs using
the standard `Std.Do` specification interface and the shared source contract. -/
@[spec] theorem foldEval_spec {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (callee : Contract source fn same R step domain)
    (initial : α) (values : List (CellValue kind)) (acc : Value accTy)
    (root : Option (NodeRef kind)) (allowed : Admissible step domain initial values)
    (post : Std.Do.PostCond (Value accTy) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (foldEval source fn same acc root)
      (fun heap => ⟨(R.Rel initial acc heap ∧ (Representation.list kind).Rel values root heap) ∧
        ∀ value finish, (R.Rel (values.foldl step initial) value finish ∧
          (Representation.list kind).Rel values root finish ∧ heap.ShapeExtends finish) →
          (post.1 value finish).down⟩) post :=
  (program_total callee initial values allowed).triple_spec
    (Env.cons acc (Env.cons root Env.empty)) post

private theorem foldl_withHeap (step : α → CellValue kind → α)
    (initial : α) (heap : Heap) (values : List (CellValue kind)) :
    values.foldl (fun state head => (step state.1 head, state.2)) (initial, heap) =
      (values.foldl step initial, heap) :=
  List.foldl_hom (fun accumulator => (accumulator, heap))
    (g₁ := step) (g₂ := fun state head => (step state.1 head, state.2))
    (l := values) (init := initial) (fun _ _ => rfl)

/-- A proved pure callback makes the same node traversal return the native
folded result in the identical heap. The contents premise refers to the real
starting heap, so this is not an unconditional pure encoding of lists. -/
theorem eval_eq_pure_of_contents {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {step : α → CellValue kind → α} {domain : α → CellValue kind → Prop}
    (encoding : α ↪ Value accTy)
    (correspondence : ∀ initial head, domain initial head →
      calleeEval source fn same (encoding initial) head = pure (encoding (step initial head)))
    (initial : α) (values : List (CellValue kind)) (root : Option (NodeRef kind))
    (heap : Heap) (allowed : Admissible step domain initial values)
    (observed : (Representation.list kind).Rel values root heap) :
    foldEval source fn same (encoding initial) root heap =
      Part.some (.ok (encoding (values.foldl step initial)), heap) := by
  have framed : Contract source fn same (Representation.ofEmbedding encoding).withHeap
      (fun state head => (step state.1 head, state.2))
      (fun state head => domain state.1 head) := by
    apply Contract.of_eval
    intro input acc head current valid related
    have encoded : encoding input.1 = acc := related.1
    subst acc
    exact ⟨encoding (step input.1 head), current,
      congrFun (correspondence input.1 head valid) current, rfl, related.2⟩
  have framedAllowed : Admissible
      (fun state head => (step state.1 head, state.2))
      (fun state head => domain state.1 head) (initial, heap) values := by
    intro processed head suffix equality
    simpa only [foldl_withHeap] using allowed processed head suffix equality
  obtain ⟨value, finish, evaluated, related, _⟩ :=
    eval_exists framed (initial, heap) values (encoding initial) root heap
      framedAllowed ⟨rfl, rfl⟩ observed
  have unchanged : encoding (values.foldl step initial) = value ∧ finish = heap := by
    simpa only [foldl_withHeap, Representation.withHeap_rel, Representation.ofEmbedding_rel]
      using related
  rcases unchanged with ⟨rfl, rfl⟩
  exact evaluated

universe v

/-- Present a fold's precondition, postcondition or bound in its two ordinary
source parameters. This is argument transport, not an executable operation. -/
def onArgs {β : Sort v} (condition : Value accTy → Option (NodeRef kind) → Heap → β) :
    Env [accTy, .option (.node kind)] → Heap → β :=
  fun args heap => condition args.head args.tail.head heap

/-- Reuse an ordinary equation for the actual fold action as a source total
contract, retaining both its result and exact initial heap. No resource fact
is involved in this mathematical correctness conversion. -/
theorem total_of_eval_eq
    {source : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {pre : Value accTy → Option (NodeRef kind) → Heap → Prop}
    {answer : Value accTy → Option (NodeRef kind) → Heap → Value accTy}
    (evaluated : ∀ actual root heap, pre actual root heap →
      foldEval source fn same actual root heap = Part.some (.ok (answer actual root heap), heap)) :
    FunctionTotal (program source fn same) (entry accTy kind signatures)
      (onArgs pre)
      (onArgs fun actual root heap value finish =>
        value = answer actual root heap ∧ finish = heap) := by
  apply FunctionTotal.iff_eval.mpr
  refine (Env.forall_cons (τ := accTy) (Γ := [.option (.node kind)]) _).mpr ?_
  intro actual
  refine (Env.forall_cons (τ := .option (.node kind)) (Γ := []) _).mpr ?_
  intro root
  refine (Env.forall_nil _).mpr ?_
  intro heap allowed
  exact ⟨answer actual root heap, heap, evaluated actual root heap allowed, rfl, rfl⟩

end Complexity.Language.List.Fold
