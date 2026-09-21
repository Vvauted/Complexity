/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Program
import Complexity.Language.Eval.Verification
import Complexity.Language.Eval.Locals.Specification

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

/-- The actual fold locals, without a mathematical inverse for the represented
accumulator or linked-list handle. -/
def loopView : Env [accTy, .option (.node kind)] ≃ Value accTy × Option (NodeRef kind) where
  toFun locals := (locals.head, locals.tail.head)
  invFun locals := Env.cons locals.1 (Env.cons locals.2 Env.empty)
  left_inv locals := by
    funext τ v
    cases v with
    | here => rfl
    | there v =>
        cases v with
        | here => rfl
        | there v => cases v
  right_inv _ := rfl

@[simp] theorem loopView_apply (locals : Env [accTy, .option (.node kind)]) :
    loopView locals = (locals.head, locals.tail.head) := rfl

@[simp] theorem loopView_symm_apply (locals : Value accTy × Option (NodeRef kind)) :
    loopView.symm locals = Env.cons locals.1 (Env.cons locals.2 Env.empty) := rfl

/-- Mathematical fold state is observed at the actual heap. The callback domain
and remaining immutable chain are retained alongside the accumulator relation. -/
def loopModelRel (R : Representation α accTy) (step : α → CellValue kind → α)
    (domain : α → CellValue kind → Prop) (model : α × List (CellValue kind))
    (locals : Value accTy × Option (NodeRef kind)) (heap : Heap) : Prop :=
  Admissible step domain model.1 model.2 ∧ R.Rel model.1 locals.1 heap ∧
    NodeRef.Contents heap locals.2 model.2

/-- The guard's mathematical decision depends only on the remaining list. -/
def loopTest (model : α × List (CellValue kind)) : Bool := !model.2.isEmpty

/-- One continuing round updates the accumulator and consumes one observed node. -/
def loopNext (step : α → CellValue kind → α)
    (model : α × List (CellValue kind)) : α × List (CellValue kind) :=
  match model.2 with
  | [] => model
  | head :: tail => (step model.1 head, tail)

/-- The actual guard retains the mathematical state and returns its emptiness
decision. This contract is independent of callback costs and RAM resources. -/
theorem guard_model_contract (program : Program signatures) (R : Representation α accTy)
    (step : α → CellValue kind → α) (domain : α → CellValue kind → Prop)
    (model : α × List (CellValue kind)) :
    Stmt.BlockSpec (Stmt.observe loopView (guard accTy kind) program)
      (loopModelRel R step domain model) (fun _ _ _ _ => False)
      (fun _ _ again output finish =>
        again = loopTest model ∧ loopModelRel R step domain model output finish) := by
  rcases model with ⟨initial, values⟩
  rintro ⟨acc, root⟩ heap ⟨allowed, related, contents⟩
  have total : TotalWP program (guard accTy kind) (fun _ => False)
      (fun (again : Bool) finish => again = loopTest (initial, values) ∧
        loopModelRel R step domain (initial, values) (loopView finish.locals) finish.heap)
      (state acc root heap) := by
    cases contents with
    | nil =>
        apply TotalWP.matchNone rfl
        apply (TotalWP.ret_iff _).mpr
        exact ⟨rfl, allowed, related, .nil⟩
    | cons found rest =>
        apply TotalWP.matchSome rfl
        apply (TotalWP.ret_iff _).mpr
        exact ⟨rfl, allowed, related, .cons found rest⟩
  simpa only [Control.Satisfies, Equiv.apply_symm_apply] using
    (TotalWP.iff_triple_observe loopView (program := program) (stmt := guard accTy kind)
      (locals := (acc, root)) (heap := heap)).mp total

/-- Existing iteration correctness supplies the next mathematical state at the
callback's actual final heap. Shape preservation transports only the immutable
remaining chain, not arbitrary mutable accumulator observations. -/
theorem iteration_model_contract {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = stepSignature accTy kind}
    {R : Representation α accTy} {step : α → CellValue kind → α}
    {domain : α → CellValue kind → Prop}
    (correct : Contract program fn same R step domain)
    (model : α × List (CellValue kind)) (active : loopTest model = true) :
    Stmt.BlockSpec (Stmt.observe loopView (iteration fn same) program)
      (loopModelRel R step domain model)
      (fun _ _ output finish => loopModelRel R step domain (loopNext step model) output finish)
      (fun _ _ _ _ _ => False) := by
  rcases model with ⟨initial, values⟩
  rintro ⟨acc, root⟩ heap ⟨allowed, related, contents⟩
  apply (TotalWP.iff_triple_observe loopView
    (normal := fun finish => loopModelRel R step domain (loopNext step (initial, values))
      (loopView finish.locals) finish.heap)
    (returned := fun _ _ => False)).mp
  cases contents with
  | nil => simp [loopTest] at active
  | cons found rest =>
      obtain ⟨headAllowed, restAllowed⟩ := (admissible_cons step domain _ _ _).mp allowed
      apply (iteration_total correct initial acc _ _ _ heap headAllowed related found).mono_post
      · rintro finish ⟨next, nextHeap, rfl, nextRelated, preserved⟩
        exact ⟨restAllowed, nextRelated, rest.mono preserved⟩
      · intro _ _ impossible
        exact impossible

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
