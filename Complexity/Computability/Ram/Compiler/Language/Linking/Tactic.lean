/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Tactic
import Complexity.Computability.Ram.Compiler.Language.Linking.Verification
import Complexity.Language.Linking.Verification
import Lean.Meta.Tactic.Simp.Main

/-!
# Using imported contracts in structural source proofs

`ram_source_call using resource, specification via embedding` transports the supplied library
contracts through the supplied actual-body embedding, then runs the existing staged call tactic.
The current goal selects realizability or cost transport. Actual results and final heaps remain
available to the continuation, and the next call still needs its own supplied contracts.
Transported contract types are simplified with `cast_eq` before structural rules infer their
preconditions or bounds. This removes only redundant signature transport, not heap dependencies.

The function-level `ram_source_realize` and `ram_source_cost` tactics also accept a final
`via embedding` clause. They retain their existing argument-name and structural-proof behavior.
These extensions only compose the existing checked transfer rules and tactics; they do not
select library contracts, unfold callees or introduce an execution or instruction-cost model.
-/

namespace Ram.LanguageCompiler.Linking.Tactic

open Lean Meta Elab Tactic

/-- Internal argument elaboration for the `via` tactics. Redundant signature casts
are removed before the structural rule infers the supplied contract's parameters. -/
syntax (name := importedContract) "ram_source_imported% " term:max : term

@[term_elab importedContract]
private def elabImportedContract : Term.TermElab := fun stx expectedType? => do
  -- Elaborate before using the expected contract so its bound is inferred without transport.
  -- Keep implicit parameters open until the existing structural rule supplies their types.
  let proof ← Term.elabTerm stx[1] none
  let type ← instantiateMVars (← inferType proof)
  let theorems ← ({} : SimpTheorems).addConst ``cast_eq
  let context ← Simp.mkContext (simpTheorems := #[theorems])
  let (normalized, _) ← Meta.simp type context
  let proof ← normalized.mkEqMP proof
  let proof ← mkExpectedTypeHint proof normalized.expr
  Term.ensureHasType expectedType? proof

private def sourceCallVia (resource specification embedding : TSyntax `term) : TacticM Unit :=
  withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
    let importedResource ←
      if target.isAppOf ``Ram.LanguageCompiler.RealizationWP then
        `(Ram.LanguageCompiler.FunctionRealizable.renameCalls $embedding $resource)
      else if target.isAppOf ``Ram.LanguageCompiler.StmtCostBound then
        `(Ram.LanguageCompiler.FunctionCostBound.renameCalls $embedding $resource)
      else
        throwError "expected a RealizationWP or StmtCostBound goal at a source call"
    evalTactic (← `(tactic|
      ram_source_call using
        (ram_source_imported% $importedResource),
        (ram_source_imported%
          (Complexity.Language.FunctionTotal.renameCalls $embedding $specification))))

/-- Transport one supplied pair of library contracts through its actual-body embedding,
then run the existing staged call proof with the actual returned value and final heap. -/
syntax (name := ramSourceCallVia) "ram_source_call" " using " term:max ", " term:max
  " via " term:max : tactic

elab_rules : tactic
  | `(tactic| ram_source_call using $resource, $specification via $embedding) =>
      sourceCallVia resource specification embedding

/-- Start a function realizability proof using a library's supplied resource and source
contracts through the given embedding. Ordinary parameter names may be omitted. -/
syntax (name := ramSourceRealizeVia) "ram_source_realize" (" (" ident* ")")?
  " using " term:max ", " term:max " via " term:max : tactic

macro_rules
  | `(tactic| ram_source_realize using $feasible, $specification via $embedding) =>
      `(tactic| ram_source_realize () using $feasible, $specification via $embedding)
  | `(tactic| ram_source_realize ($names:ident*) using $feasible, $specification via $embedding) =>
      `(tactic| ram_source_realize ($names*) using
        (ram_source_imported%
          (Ram.LanguageCompiler.FunctionRealizable.renameCalls $embedding $feasible)),
        (ram_source_imported%
          (Complexity.Language.FunctionTotal.renameCalls $embedding $specification)))

/-- Start a function cost proof using a library's supplied bound through its actual-body
embedding. This delegates all structural accounting to the existing cost tactic. -/
syntax (name := ramSourceCostVia) "ram_source_cost" (" (" ident* ")")?
  " using " term:max " via " term:max : tactic

macro_rules
  | `(tactic| ram_source_cost using $bounded via $embedding) =>
      `(tactic| ram_source_cost () using $bounded via $embedding)
  | `(tactic| ram_source_cost ($names:ident*) using $bounded via $embedding) =>
      `(tactic| ram_source_cost ($names*) using
        (ram_source_imported%
          (Ram.LanguageCompiler.FunctionCostBound.renameCalls $embedding $bounded)))

end Ram.LanguageCompiler.Linking.Tactic
