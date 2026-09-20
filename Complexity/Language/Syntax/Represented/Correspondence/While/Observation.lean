/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Correspondence.While.Identity
import Complexity.Language.Eval.Locals.Specification

/-!
# Native proof entries for complete identity locals

These observations map the output of an existing named guard or body. They keep
its actual control, heap and local completion value: no source statement or
alternative implementation is generated. The checked coordinate equivalence
is available only for complete identity-represented locals. Other representations
continue to use heap-indexed relational contracts, not an invented inverse.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

/-- Expose native mathematical-local triples for the same actual completion
actions when their complete local representation has a checked inverse. -/
def completionObservationDeclarations (loop : WhileLocalRegistration)
    (localResult : TSyntax `term) : TermElabM (Array Syntax) := do
  unless ← loop.hasIdentityVisible do return #[]
  let site ← loop.site
  let member (suffix : Name) := mkIdent (site.name ++ suffix)
  let modelType := member `Model
  let localsType := member `Locals
  let visibleType := member `Visible
  let visible := member `visible
  let pending := member `pending
  let entry := member `entry
  let equivalence := member `modelEquiv
  let relationIff := member `visibleModelRel_iff
  let guard := member `guard
  let body := member `body
  let guardContract := member `guard_completion_contract
  let bodyContract := member `body_completion_contract
  let guardModelContract := member `guard_model_contract
  let bodyModelContract := member `body_model_contract
  let guardAction := member `guard_model_action
  let bodyAction := member `body_model_action
  let guardIff := member `guard_model_contract_iff
  let bodyIff := member `body_model_contract_iff
  let sourceResult ← termOfExpr (coreTypeExpr site.result)
  let model := mkIdent (← mkFreshUserName `model)
  let start := mkIdent (← mkFreshUserName `start)
  let actual := mkIdent (← mkFreshUserName `actual)
  let invoke (name : TSyntax `ident) (input : TSyntax `term) := do
    let locals ← `($entry:ident $input)
    pure (Lean.Syntax.mkApp ⟨name.raw⟩ (← sourceFields site.scope.size locals))
  let guardInvocation ← invoke guard ⟨start.raw⟩
  let bodyInvocation ← invoke body ⟨start.raw⟩
  let guardModelInvocation ← invoke guard (← `($equivalence:ident $model:ident))
  let bodyModelInvocation ← invoke body (← `($equivalence:ident $model:ident))
  let guardProjection ← `(fun ($actual:ident : $localsType:ident) =>
    ($equivalence:ident).symm ($visible:ident $actual:ident))
  let bodyProjection ← `(fun ($actual:ident : $localsType:ident) =>
    ($pending:ident $actual:ident,
      ($equivalence:ident).symm ($visible:ident $actual:ident)))
  let guardMapped ← `(fun ($start:ident : $visibleType:ident) =>
    (fun outcome => (outcome.1, $guardProjection outcome.2)) <$> $guardInvocation)
  let bodyMapped ← `(fun ($start:ident : $visibleType:ident) =>
    (fun outcome => (outcome.1, $bodyProjection outcome.2)) <$> $bodyInvocation)
  let guardNormal ← `(fun (_ : $visibleType:ident) (_ : Complexity.Language.Heap)
    (_ : $modelType:ident) (_ : Complexity.Language.Heap) => False)
  let guardReturned ← `(fun (_ : $visibleType:ident) (heap : Complexity.Language.Heap)
    (again : Bool) (output : $modelType:ident) (finish : Complexity.Language.Heap) =>
      ∃ next, output = encode next ∧ post heap again next finish)
  let bodyNormal ← `(fun (_ : $visibleType:ident) (heap : Complexity.Language.Heap)
    (output : Option $localResult × $modelType:ident) (finish : Complexity.Language.Heap) =>
      match output.1 with
      | none => ∃ next, output.2 = encode next ∧ normal heap next finish
      | some value => ∃ next, output.2 = encode next ∧ completed heap value next finish)
  let bodyReturned ← `(fun (_ : $visibleType:ident) (_ : Complexity.Language.Heap)
    (_ : Complexity.Language.Value $sourceResult)
    (_ : Option $localResult × $modelType:ident) (_ : Complexity.Language.Heap) => False)
  return #[
    (← `(command|
      /-- Observe the same guard in mathematical coordinates. Control and the
      actual final heap are untouched; this is not another source implementation. -/
      noncomputable def $(whileDeclarationName guardAction):ident ($model:ident : $modelType:ident) :
          StateT Complexity.Language.Heap Part
            (Complexity.Language.Control .bool × $modelType:ident) :=
        (fun outcome => (outcome.1, $guardProjection outcome.2)) <$> $guardModelInvocation)).raw,
    (← `(command|
      /-- Observe the same body and its actual local completion slot. Mapping
      the result neither changes source control nor performs heap cleanup. -/
      noncomputable def $(whileDeclarationName bodyAction):ident ($model:ident : $modelType:ident) :
          StateT Complexity.Language.Heap Part
            (Complexity.Language.Control $sourceResult ×
              (Option $localResult × $modelType:ident)) :=
        (fun outcome => (outcome.1, $bodyProjection outcome.2)) <$> $bodyModelInvocation)).raw,
    (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Prove the actual guard contract directly from ordinary mathematical
      locals. The input-coordinate and output-representation transport is shared. -/
      theorem $(whileDeclarationName guardIff):ident {Index : Type}
          (encode : Index → $modelType:ident) (index : Index)
          (pre : Complexity.Language.Heap → Prop)
          (post : Complexity.Language.Heap → Bool → Index → Complexity.Language.Heap → Prop) :
          $guardModelContract:ident encode index pre post ↔
            ∀ heap, pre heap →
              Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
                (ps := .arg Complexity.Language.Heap .pure)
                ($guardAction:ident (encode index)) (fun current => ⟨current = heap⟩)
                (fun outcome finish => ⟨match outcome.1 with
                  | .normal => False
                  | .returned again =>
                      ∃ next, outcome.2 = encode next ∧ post heap again next finish
                  | .fault _ => False⟩, ⟨⟩) := by
        have mapped := Complexity.Language.Stmt.BlockSpec.map_iff
          (result := .bool)
          (action := fun ($start:ident : $visibleType:ident) => $guardInvocation)
          (pre := fun locals heap => locals = $equivalence:ident (encode index) ∧ pre heap)
          $guardProjection $guardNormal $guardReturned
        have fixed := Complexity.Language.Stmt.BlockSpec.input_eq_iff
          (result := .bool)
          (action := $guardMapped) (normal := $guardNormal) (returned := $guardReturned)
          ($equivalence:ident (encode index)) pre
        unfold $guardAction:ident
        have transported := mapped.symm.trans fixed
        constructor
        · intro specification heap initial
          have checked := transported.mp (by
            simpa only [$guardModelContract:ident, $guardContract:ident,
              $relationIff:ident, Equiv.symm_apply_eq] using specification) heap initial
          refine checked.mono (fun _ same => same) ?_
          constructor
          · rintro ⟨control, output⟩ finish property
            cases control <;> exact property
          · trivial
        · intro specification
          have checked := transported.mpr (by
            intro heap initial
            refine (specification heap initial).mono (fun _ same => same) ?_
            constructor
            · rintro ⟨control, output⟩ finish property
              cases control <;> exact property
            · trivial)
          simpa only [$guardModelContract:ident, $guardContract:ident,
            $relationIff:ident, Equiv.symm_apply_eq] using checked)).raw,
    (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Prove the actual body contract using mathematical locals and the real
      completion value. Continuing and completed outcomes retain the actual heap. -/
      theorem $(whileDeclarationName bodyIff):ident {Index : Type}
          (encode : Index → $modelType:ident) (index : Index)
          (pre : Complexity.Language.Heap → Prop)
          (normal : Complexity.Language.Heap → Index → Complexity.Language.Heap → Prop)
          (completed : Complexity.Language.Heap → $localResult → Index →
            Complexity.Language.Heap → Prop) :
          $bodyModelContract:ident encode index pre normal completed ↔
            ∀ heap, pre heap →
              Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
                (ps := .arg Complexity.Language.Heap .pure)
                ($bodyAction:ident (encode index)) (fun current => ⟨current = heap⟩)
                (fun outcome finish => ⟨match outcome.1 with
                  | .normal => match outcome.2.1 with
                    | none => ∃ next, outcome.2.2 = encode next ∧ normal heap next finish
                    | some value =>
                        ∃ next, outcome.2.2 = encode next ∧ completed heap value next finish
                  | .returned _ => False
                  | .fault _ => False⟩, ⟨⟩) := by
        have mapped := Complexity.Language.Stmt.BlockSpec.map_iff
          (result := $sourceResult)
          (action := fun ($start:ident : $visibleType:ident) => $bodyInvocation)
          (pre := fun locals heap => locals = $equivalence:ident (encode index) ∧ pre heap)
          $bodyProjection $bodyNormal $bodyReturned
        have fixed := Complexity.Language.Stmt.BlockSpec.input_eq_iff
          (result := $sourceResult)
          (action := $bodyMapped) (normal := $bodyNormal) (returned := $bodyReturned)
          ($equivalence:ident (encode index)) pre
        unfold $bodyAction:ident
        have transported := mapped.symm.trans fixed
        constructor
        · intro specification heap initial
          have checked := transported.mp (by
            simpa only [$bodyModelContract:ident, $bodyContract:ident,
              $relationIff:ident, Equiv.symm_apply_eq] using specification) heap initial
          refine checked.mono (fun _ same => same) ?_
          constructor
          · rintro ⟨control, output⟩ finish property
            cases control <;> exact property
          · trivial
        · intro specification
          have checked := transported.mpr (by
            intro heap initial
            refine (specification heap initial).mono (fun _ same => same) ?_
            constructor
            · rintro ⟨control, output⟩ finish property
              cases control <;> exact property
            · trivial)
          simpa only [$bodyModelContract:ident, $bodyContract:ident,
            $relationIff:ident, Equiv.symm_apply_eq] using checked)).raw]

end Internal

end Complexity.Language.Syntax.Represented
