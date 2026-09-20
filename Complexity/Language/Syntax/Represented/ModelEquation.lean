/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Basic
import Mathlib.Data.Option.Basic
import Lean.Elab.Tactic.Conv.Simp
import Lean.Elab.Tactic.Conv.Unfold

/-!
# Mathematical equations for represented completion loops

An optional proof equation simplifies the generated mathematical function, not
its actual source action. State maps cross pure branches by existing equalities;
the simplifier retains the range iteration and does not unfold recursive calls.
No equation from this pass is registered in the global simp set.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

namespace Internal

private def mapBranch (expression : Expr) : SimpM Simp.Step := do
  unless expression.isAppOfArity ``Prod.map 7 do return .continue
  let projection := expression.appFn!
  let value := expression.appArg!
  let arguments := value.getAppArgs
  let proof ← if value.isAppOfArity ``Option.elim 5 then
      mkEqSymm (← mkAppOptM ``Option.elim_comp
        #[none, none, none, some projection, some arguments[4]!,
          some arguments[3]!, some arguments[2]!])
    else if value.isAppOfArity ``ite 5 then
      mkAppOptM ``apply_ite
        #[none, none, some projection, some arguments[1]!, some arguments[2]!,
          some arguments[3]!, some arguments[4]!]
    else return .continue
  return .visit { expr := (← inferType proof).appArg!, proof? := some proof }

private def mathematicalSimp (expression : Expr) : MetaM Simp.Result := do
  let mut rules : SimpTheorems := {}
  rules ← rules.addDeclToUnfold ``Id.run
  for name in #[``Option.elim_none, ``Option.elim_some, ``Prod.map_apply] do
    rules ← rules.addConst name
  let context ← Simp.mkContext
    (config := { proj := false, implicitDefEqProofs := false })
    (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let standard := Simp.mkDefaultMethodsCore #[]
  let methods := { standard with post := fun expression => do
    -- With projection reduction disabled, class projections need their own
    -- administrative reduction. Keep it restricted to the identity monad.
    if (expression.isAppOfArity ``Pure.pure 4 || expression.isAppOfArity ``Bind.bind 6) &&
        (expression.getArg! 0).isConstOf ``Id then
      if let some reduced ← withReducibleAndInstances <| unfoldDefinition? expression then
        return .visit { expr := reduced }
    match ← mapBranch expression with
    | .continue none =>
        -- Reduce concrete tuple fields only after simplifying their receiver.
        -- Unfolding a state map through a projection beforehand duplicates its branches.
        if let .proj ``Prod index value := expression then
          if value.isAppOfArity ``Prod.mk 4 then
            return .visit { expr := value.getAppArgs[index + 2]! }
        standard.post expression
    | result => return result }
  return (← Simp.main expression context (methods := methods)).1

elab "source_model_simp" : conv => Lean.Elab.Tactic.withMainContext do
  Lean.Elab.Tactic.Conv.applySimpResult (← mathematicalSimp (← Lean.Elab.Tactic.Conv.getLhs))

private partial def hasCompletionRange (ranges : Array RangeRegistration)
    (calls : Array Trace) : Bool := calls.any fun call =>
  match call with
  | .conditional _ yes no .. | .optionMatch _ _ yes no .. =>
      hasCompletionRange ranges yes || hasCompletionRange ranges no
  | .valueBlock body _ _ => hasCompletionRange ranges body
  | .range tag .. =>
      match ranges.find? (·.tag == tag) with
      | some { model := .completion .., .. } => true
      | some range => hasCompletionRange ranges range.body
      | _ => false
  | .call _ => false

/-- Publish a checked mathematical equation for a model with a local-completion
range. Expand the function once; later simplification never unfolds its calls. -/
def modelEquationDeclaration? (names : DeclarationNames) (fn : Function)
    (model : FunctionModel) (ranges : Array RangeRegistration) :
    TermElabM (Option Syntax) := do
  unless hasCompletionRange ranges model.calls do return none
  let native := modelName names fn.name
  let equation := fieldName names.publicFamily fn.name "_model_eq"
  let arguments := fn.parameters.map fun parameter => (⟨parameter.name.raw⟩ : TSyntax `term)
  let applied := Lean.Syntax.mkApp ⟨native.raw⟩ arguments
  let mut proof ← `(source_conversion% $applied => {
    unfold $native:ident; source_model_simp })
  for parameter in fn.parameters.reverse do
    let type ← termOfExpr parameter.type.nativeType
    proof ← `(fun ($(parameter.name):ident : $type) => $proof)
  return some (← `(command| source_equation% $equation:ident := $proof)).raw

end Internal

end Complexity.Language.Syntax.Represented
