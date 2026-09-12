/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Range
import Lean.Elab.Tactic.Induction
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Meta.Tactic.FunInd

/-!
# Correspondence for the buffer-free total frontend

The frontend emits an executable Lean definition and the usual independently
interpreted source body from the same checked block. This internal tactic uses
Lean's functional induction principle for the executable definition: its
recursive hypotheses therefore follow the termination proof already checked by
Lean. It unfolds the source action once, then composes those hypotheses and
previously proved callee correspondences using ordinary monad laws.
Native products and options are ordinary Lean values; case splitting uses the
same source match equation and native match, without a second evaluator or a
payload in the `none` case.

`source_pure_simp [P.f]` exposes ordinary fold mathematics for always-continuing
finite ranges. Its local simplification procedure extracts the mutable step
from the actual callback, then checks that the existing range theorem applies
definitionally. It does not assume independence from the return flag or cursor.
The unique empty lexical tail is removed by a fold homomorphism; genuinely
coupled mutable values remain together.

This is not an interpreter, a termination oracle, or a native callback in the
source program. A failed correspondence remains a failed declaration.
-/

namespace Complexity.Language.Syntax

open Lean Meta Elab Tactic

/-- Instantiate the proved range equation from the actual native callback.
This procedure is enabled only by the explicit pure-mathematics tactic. -/
simproc_decl reducePureRange (@ForIn.forIn Id _ _ _ _ _ _ _) := fun expression => do
  let_expr ForIn.forIn _ collectionType _ _ _ collection initial body := expression
    | return .continue
  unless collectionType.isConstOf ``Std.Legacy.Range do return .continue
  let initialType ← whnf (← inferType initial)
  let_expr Prod flagType restType := initialType | return .continue
  let flagType ← whnf flagType
  let_expr Option result := flagType | return .continue
  let restType ← whnf restType
  let_expr Prod indexType mutableType := restType | return .continue
  unless indexType.isConstOf ``Nat do return .continue
  let initialMutable := mkProj ``Prod 1 (mkProj ``Prod 1 initial)
  let start ← mkProjection collection `start
  let stop ← mkProjection collection `stop
  let stride ← mkProjection collection `step
  let positive ← mkProjection collection `step_pos
  let next? ← withLocalDeclD `index (mkConst ``Nat) fun index =>
    withLocalDeclD `mutable mutableType fun mutable => do
      let noneValue ← mkAppOptM ``Option.none #[some result]
      let state ← mkAppM ``Prod.mk #[noneValue, ← mkAppM ``Prod.mk #[index, mutable]]
      let iteration ← whnf (mkApp2 body index state)
      let_expr ForInStep.yield _ outcome := iteration | return none
      let next ← whnf (mkProj ``Prod 1 (mkProj ``Prod 1 outcome))
      return some (← mkLambdaFVars #[index, mutable] next)
  let some next := next? | return .continue
  let proof ← if ← isDefEq stride (mkNatLit 1) then
      mkAppOptM ``Complexity.Language.Stmt.forIn_range_yield_eq_foldl
        #[some mutableType, some result, some next, some start, some stop, some initialMutable]
    else
      mkAppOptM ``Complexity.Language.Stmt.forIn_range_step_yield_eq_foldl
        #[some mutableType, some result, some next, some start, some stop,
          some stride, some positive, some initialMutable]
  let some (_, lhs, rhs) := (← inferType proof).eq? | return .continue
  unless ← withTransparency .default (isDefEq lhs expression) do return .continue
  return .visit { expr := ← instantiateMVars rhs, proof? := ← instantiateMVars proof }

/-- Reduce selected native source functions to ordinary fold mathematics.
Early-return loops remain native iterations; no mathematical callee is unfolded
unless named explicitly. -/
syntax (name := sourcePureSimp) "source_pure_simp " "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| source_pure_simp [$functions:ident,*]) => do
      let facts ← functions.getElems.mapM fun function =>
        `(Lean.Parser.Tactic.simpLemma| $function:ident)
      evalTactic (← `(tactic|
        simp only [Id.run, Id.instMonad, Option.elim_none, reducePureRange,
          Complexity.Language.Stmt.foldl_fst_unit, Nat.add_eq, Nat.mul_eq,
          Nat.sub_eq, Nat.sub_zero, $facts,*]))

syntax (name := sourcePureCorrespondence)
  "source_pure_correspondence " term " using " ident " [" ident,* "]" : tactic

syntax (name := sourcePureCorrespondenceLoops)
  "source_pure_correspondence " term " using " ident " [" ident,* "]"
  " ranges% " "[" ident,* "]" " blocks% " "[" ident,* "]" : tactic

syntax (name := sourcePureCorrespondenceEncoded)
  "source_pure_correspondence " term " using " ident " [" ident,* "]"
  " encodings% " "[" ident,* "]" : tactic

syntax (name := sourcePureCorrespondenceEncodedLoops)
  "source_pure_correspondence " term " using " ident " [" ident,* "]"
  " encodings% " "[" ident,* "]"
  " ranges% " "[" ident,* "]" " blocks% " "[" ident,* "]" : tactic

private partial def closePureBranches (callees loopRules bodyRules : Array (TSyntax `ident)) :
    TacticM Unit := do
  let facts ← (callees ++ bodyRules).mapM fun callee => `(Lean.Parser.Tactic.simpLemma| $callee:ident)
  evalTactic (← `(tactic| all_goals intros))
  evalTactic (← `(tactic| all_goals try rfl))
  evalTactic (← `(tactic| all_goals try
    (simp (config := { zetaDelta := true, failIfUnchanged := false }) only
      [Nat.add_eq] <;> omega)))
  evalTactic (← `(tactic| all_goals
    simp_all (config := { failIfUnchanged := false })
      [Id.run, Id.instMonad, MonadLift.monadLift, ExceptT.lift_pure, $facts,*]))
  evalTactic (← `(tactic| all_goals try rfl))
  evalTactic (← `(tactic| all_goals try
    (simp (config := { zetaDelta := true, failIfUnchanged := false }) only
      [Nat.add_eq] <;> omega)))
  let goals ← getGoals
  setGoals []
  for goal in goals do
    if ← goal.isAssigned then continue
    setGoals [goal]
    let mut rewritten := false
    for loop in loopRules do
      let saved ← saveState
      try
        evalTactic (← `(tactic| rw [$loop:ident]))
        rewritten := true
        break
      catch _ => saved.restore
    unless rewritten do
      evalTactic (← `(tactic| split))
    closePureBranches callees loopRules bodyRules

/-- Compose already proved callees and nested ranges in one generated source
block. The enclosing native definition is not unfolded or assumed correct. -/
syntax (name := sourcePureBlockCorrespondence)
  "source_pure_block_correspondence " "[" ident,* "]"
  " ranges% " "[" ident,* "]" " blocks% " "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| source_pure_block_correspondence [$facts:ident,*]
      ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*]) =>
      closePureBranches facts.getElems loopRules.getElems bodyRules.getElems

private def pureCorrespondence (application : TSyntax `term) (equation : TSyntax `ident)
    (callees loopRules bodyRules : Array (TSyntax `ident)) : TacticM Unit := withMainContext do
  let value ← Term.elabTerm application none
  let .const name _ := value.getAppFn
    | throwErrorAt application "expected a fully applied generated native function"
  if (← Meta.getFunIndInfo? false true name).isSome then
    evalTactic (← `(tactic| fun_induction $application:term))
  else
    let function := mkCIdent name
    evalTactic (← `(tactic| conv => rhs; unfold $function:ident))
  evalTactic (← `(tactic| all_goals rw [$equation:ident]))
  closePureBranches callees loopRules bodyRules

elab_rules : tactic
  | `(tactic| source_pure_correspondence $application:term using $equation:ident
      [$callees:ident,*]) => pureCorrespondence application equation callees.getElems #[] #[]
  | `(tactic| source_pure_correspondence $application:term using $equation:ident
      [$callees:ident,*] ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*]) =>
      pureCorrespondence application equation callees.getElems loopRules.getElems bodyRules.getElems
  | `(tactic| source_pure_correspondence $application:term using $equation:ident
      [$callees:ident,*] encodings% [$encodings:ident,*]) =>
      pureCorrespondence application equation (callees.getElems ++ encodings.getElems) #[] #[]
  | `(tactic| source_pure_correspondence $application:term using $equation:ident
      [$callees:ident,*] encodings% [$encodings:ident,*]
      ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*]) =>
      pureCorrespondence application equation (callees.getElems ++ encodings.getElems)
        loopRules.getElems bodyRules.getElems

end Complexity.Language.Syntax
