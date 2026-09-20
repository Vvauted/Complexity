/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.While.Observation
import Complexity.Language.Eval.Locals.LocalReturn.Models

/-!
# Mathematical local contracts for while completion

The source bindings use the same heap-indexed model as ordinary while rounds.
An author-selected index describes mathematical progress; its encoding supplies
the local values, not another implementation. Supplied contracts prove each real
guard and body. Effectful guards supply an intermediate mathematical index and
actual heap through a preparation relation. The preserving-guard interface is
a specialization, not a separate loop proof.

The body may change the heap. Only continuing rounds preserve the invariant and
decrease. Completed rounds instead establish their result postcondition. No pure
body transition, heap frame, array snapshot or cost is inferred.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

/-- Read the actual pending payload type, without inverting the source `Value` family. -/
private def completionResultType (pending : Name) : TermElabM (TSyntax `term) := do
  forallTelescope (← inferType (mkConst pending)) fun _ result => do
    match ← whnf result with
    | .app (.const ``Option _) payload => termOfExpr payload
    | _ => throwError "the actual local completion slot must have an optional result"

/-- Generate contract-based mathematical observations for the actual locally
returning loop. Its body need not have a total pure mathematical function. -/
def completionWhileDeclarations (loop : WhileLocalRegistration) : TermElabM (Array Syntax) := do
  let site ← loop.site
  unless site.localReturn do throwError "expected an actual locally returning while"
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let modelType := member `Model
  let modelRel := member `modelRel
  let visibleType := member `Visible
  let visible := member `visible
  let pending := member `pending
  let entry := member `entry
  let visibleModelRel := member `visibleModelRel
  let guardContract := member `guard_completion_contract
  let bodyContract := member `body_completion_contract
  let contract := member `completion_contract
  let relContract := member `completion_rel_contract
  let guardModelContract := member `guard_model_contract
  let bodyModelContract := member `body_model_contract
  let modelContract := member `model_completion_contract
  let modelEffectsContract := member `model_completion_effects_contract
  let resultType ← completionResultType pending.getId
  let mut declarations ← whileModelDeclarations loop
  declarations := declarations.push (← `(command|
    /-- Observe mathematical locals at a visible completion boundary's actual heap. -/
    def $(whileDeclarationName visibleModelRel):ident (model : $modelType:ident)
        (locals : $visibleType:ident) (heap : Complexity.Language.Heap) : Prop :=
      $modelRel:ident model ($entry:ident locals) heap)).raw
  declarations := declarations ++ (← completionIdentityDeclarations loop)
  declarations := declarations ++ #[
    (← `(command|
      /-- A supplied actual guard contract, expressed through mathematical indices.
      Each output observation is made at the real final heap. -/
      abbrev $(whileDeclarationName guardModelContract):ident {Index : Type}
          (encode : Index → $modelType:ident) (index : Index)
          (pre : Complexity.Language.Heap → Prop)
          (post : Complexity.Language.Heap → Bool → Index → Complexity.Language.Heap → Prop) : Prop :=
        $guardContract:ident
          (fun locals heap => $visibleModelRel:ident (encode index) locals heap ∧ pre heap)
          (fun _ heap again output finish => ∃ next,
            $visibleModelRel:ident (encode next) output finish ∧ post heap again next finish))).raw,
    (← `(command|
      /-- A supplied body contract may change the heap or complete the local block.
      Continuing and completed results have separate mathematical postconditions. -/
      abbrev $(whileDeclarationName bodyModelContract):ident {Index : Type}
          (encode : Index → $modelType:ident) (index : Index)
          (pre : Complexity.Language.Heap → Prop)
          (normal : Complexity.Language.Heap → Index → Complexity.Language.Heap → Prop)
          (completed : Complexity.Language.Heap → $resultType → Index →
            Complexity.Language.Heap → Prop) : Prop :=
        $bodyContract:ident
          (fun locals heap => $visibleModelRel:ident (encode index) locals heap ∧ pre heap)
          (fun _ heap output finish => ∃ next,
            $visibleModelRel:ident (encode next) output finish ∧ normal heap next finish)
          (fun _ heap result output finish => ∃ next,
            $visibleModelRel:ident (encode next) output finish ∧
              completed heap result next finish))).raw,
    (← `(command|
      /-- Compose mathematical contracts at the actual heaps before and after
      an effectful guard. Continuing rounds decrease from the state before the
      guard; a false guard or a completed body establishes the final condition. -/
      theorem $(whileDeclarationName modelEffectsContract):ident {Index : Type}
          (encode : Index → $modelType:ident)
          (invariant : Index → Complexity.Language.Heap → Prop)
          (prepared : Index → Complexity.Language.Heap → Index → Complexity.Language.Heap → Prop)
          (step : Index → Index → Prop) {relation : Index → Index → Prop}
          (wellFounded : WellFounded relation)
          (normal : Index → Complexity.Language.Heap → Prop)
          (completed : $resultType → Index → Complexity.Language.Heap → Prop)
          (guardSpec : ∀ index heap, invariant index heap →
            $guardModelContract:ident encode index (fun current => current = heap)
              (fun initial again next finish =>
                if again then prepared index initial next finish else normal next finish))
          (bodySpec : ∀ index heap, invariant index heap →
            ∀ tested after, prepared index heap tested after →
              $bodyModelContract:ident encode tested (fun current => current = after)
                (fun _ next finish => step index next ∧ invariant next finish)
                (fun _ => completed))
          (decreases : ∀ index heap, invariant index heap →
            ∀ tested after, prepared index heap tested after →
              ∀ next, step index next → relation next index)
          (index : Index) :
          $contract:ident
            (fun locals heap => $visibleModelRel:ident (encode index) locals heap ∧
              invariant index heap)
            (fun _ _ output finish => ∃ next,
              $visibleModelRel:ident (encode next) output finish ∧ normal next finish)
            (fun _ _ result output finish => ∃ next,
              $visibleModelRel:ident (encode next) output finish ∧ completed result next finish) := by
        apply $relContract:ident
          (fun index locals heap => $visibleModelRel:ident (encode index) locals heap ∧
            invariant index heap)
          (fun _ => True) wellFounded
          (fun index _ initial output finish => ∃ tested,
            $visibleModelRel:ident (encode tested) output finish ∧
              prepared index initial tested finish)
          (fun output finish => ∃ next,
            $visibleModelRel:ident (encode next) output finish ∧ normal next finish)
          (fun result output finish => ∃ next,
            $visibleModelRel:ident (encode next) output finish ∧ completed result next finish)
          _ _ index trivial
        · intro current _
          exact Complexity.Language.Stmt.BlockSpec.guard_model_effects $visible:ident
            (fun index => $visibleModelRel:ident (encode index))
            invariant normal prepared guardSpec current
        · intro current _ heap _ initial
          have checked := Complexity.Language.Stmt.BlockSpec.body_model_effects
            $visible:ident $pending:ident
            (fun index => $visibleModelRel:ident (encode index))
            invariant prepared step relation completed
            (by
              intro index heap valid tested after ready
              refine Complexity.Language.Stmt.BlockSpec.mono
                (bodySpec index heap valid tested after ready)
                (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible)
              intro _ _ output finish _ property
              cases stopped : $pending:ident output <;>
                simpa only [stopped] using property)
            decreases current heap initial.2
          refine Complexity.Language.Stmt.BlockSpec.mono checked
            (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible)
          intro _ _ output finish _ property
          cases stopped : $pending:ident output <;>
            simpa only [stopped] using property)).raw,
    (← `(command|
      /-- Compose the actual loop from mathematical local contracts. The supplied
      guard preserves the index and heap; only a continuing body needs descent.
      The step relation describes mathematical progress, not a pure implementation. -/
      theorem $(whileDeclarationName modelContract):ident {Index : Type}
          (encode : Index → $modelType:ident) (test : Index → Bool)
          (invariant : Index → Complexity.Language.Heap → Prop)
          (step : Index → Index → Prop) {relation : Index → Index → Prop}
          (wellFounded : WellFounded relation)
          (normal : Index → Complexity.Language.Heap → Prop)
          (completed : $resultType → Index → Complexity.Language.Heap → Prop)
          (guardSpec : ∀ index heap, invariant index heap →
            $guardModelContract:ident encode index (fun current => current = heap)
              (fun heap again next finish => again = test index ∧ next = index ∧ finish = heap))
          (bodySpec : ∀ index heap, invariant index heap → test index = true →
            $bodyModelContract:ident encode index (fun current => current = heap)
              (fun _ next finish => step index next ∧ invariant next finish)
              (fun _ => completed))
          (decreases : ∀ index next heap, invariant index heap → test index = true →
            step index next → relation next index)
          (exit : ∀ index heap, invariant index heap → test index = false → normal index heap)
          (index : Index) :
          $contract:ident
            (fun locals heap => $visibleModelRel:ident (encode index) locals heap ∧
              invariant index heap)
            (fun _ _ output finish => ∃ next,
              $visibleModelRel:ident (encode next) output finish ∧ normal next finish)
            (fun _ _ result output finish => ∃ next,
              $visibleModelRel:ident (encode next) output finish ∧ completed result next finish) := by
        apply $modelEffectsContract:ident encode invariant
          (fun current initial tested after =>
            tested = current ∧ after = initial ∧ test current = true)
          step wellFounded normal completed _ _ _ index
        · intro current heap valid
          refine Complexity.Language.Stmt.BlockSpec.mono (guardSpec current heap valid)
            (fun _ _ initial => initial) (fun _ _ _ _ _ impossible => impossible) ?_
          rintro _ initial again output finish ⟨_, sameInitial⟩
            ⟨next, represented, decision, sameModel, sameHeap⟩
          subst next initial finish
          refine ⟨current, represented, ?_⟩
          cases again with
          | true => exact ⟨rfl, rfl, decision.symm⟩
          | false => exact exit current heap valid decision.symm
        · intro current heap valid tested after ready
          obtain ⟨sameModel, sameHeap, active⟩ := ready
          subst tested after
          exact bodySpec current heap valid active
        · intro current heap valid tested after ready next advanced
          obtain ⟨sameModel, sameHeap, active⟩ := ready
          subst tested after
          exact decreases current next heap valid active advanced)).raw]
  return declarations ++ (← completionObservationDeclarations loop resultType)

end Internal

end Complexity.Language.Syntax.Represented
