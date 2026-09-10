/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Lean.Elab.Tactic.Induction
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Meta.Tactic.FunInd

/-!
# Correspondence for the scalar total frontend

The frontend emits an executable Lean definition and the usual independently
interpreted source body from the same checked block. This internal tactic uses
Lean's functional induction principle for the executable definition: its
recursive hypotheses therefore follow the termination proof already checked by
Lean. It unfolds the source action once, then composes those hypotheses and
previously proved callee correspondences using ordinary monad laws.

This is not an interpreter, a termination oracle, or a native callback in the
source program. A failed correspondence remains a failed declaration.
-/

namespace Complexity.Language.Syntax

open Lean Elab Tactic

syntax (name := sourcePureCorrespondence)
  "source_pure_correspondence " term " using " ident " [" ident,* "]" : tactic

private partial def closePureBranches (callees : Array (TSyntax `ident)) : TacticM Unit := do
  let facts ← callees.mapM fun callee => `(Lean.Parser.Tactic.simpLemma| $callee:ident)
  evalTactic (← `(tactic| all_goals try rfl))
  evalTactic (← `(tactic| all_goals simp_all [Id.run, Id.instMonad, $facts,*]))
  evalTactic (← `(tactic| all_goals try rfl))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals split))
    closePureBranches callees

elab_rules : tactic
  | `(tactic| source_pure_correspondence $application:term using $equation:ident
      [$callees:ident,*]) => withMainContext do
      let value ← Term.elabTerm application none
      let .const name _ := value.getAppFn
        | throwErrorAt application "expected a fully applied generated native function"
      if (← Meta.getFunIndInfo? false true name).isSome then
        evalTactic (← `(tactic| fun_induction $application:term))
      else
        let function := mkCIdent name
        evalTactic (← `(tactic| conv => rhs; unfold $function:ident))
      evalTactic (← `(tactic| all_goals rw [$equation:ident]))
      closePureBranches callees.getElems

end Complexity.Language.Syntax
