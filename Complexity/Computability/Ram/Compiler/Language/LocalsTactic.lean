/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Generated source-loop coordinate normalization

`ram_source_locals Family.function_loop1` rewrites the target through that loop's
registered coordinate equations. Ordinary locations such as `at h`, `at h ⊢`
and `at *` select exactly the hypotheses and target to rewrite.

The registration contains only already checked view and native encoding rules,
including the selected range's frozen endpoint projections. The loop's `Code`
declaration is its identity key, not an unfolding rule. No body, callee, invariant,
value-range predicate or compiler cost is unfolded. This tactic performs no
arithmetic or assumption search; mathematical obligations remain for the author.
-/

namespace Ram.LanguageCompiler.LocalsTactic

open Lean Meta Elab Tactic Parser.Tactic

private def normalize (site : TSyntax `ident)
    (location : Option (TSyntax ``Lean.Parser.Tactic.location)) : TacticM Unit :=
  withMainContext do
    let code ← resolveGlobalConstNoOverload (mkIdentFrom site (site.getId ++ `Code))
    let some information := Complexity.Language.Syntax.getLoopCoordinates? (← getEnv) code
      | throwErrorAt site "'{site.getId}' is not a registered source loop"
    let coordinateRules := information.rules ++ #[
      ``Equiv.refl_apply, ``Equiv.refl_symm,
      ``Equiv.apply_symm_apply, ``Equiv.symm_apply_apply,
      ``Equiv.toFun_as_coe, ``Equiv.invFun_as_coe,
      ``Function.Embedding.toFun_eq_coe,
      ``Function.Embedding.coe_refl, ``Function.Embedding.coe_prodMap,
      ``Prod.map, ``Prod.mk.eta, ``id]
    Ram.LanguageCompiler.Tactic.normalizeSourceCoordinates coordinateRules location

/-- Normalize only the selected source loop's proof coordinates. Optional
standard locations restrict the rewrite; unchanged locations are accepted. -/
syntax (name := ramSourceLocals) "ram_source_locals " ident (location)? : tactic

elab_rules : tactic
  | `(tactic| ram_source_locals $site:ident $[$loc:location]?) => normalize site loc

end Ram.LanguageCompiler.LocalsTactic
