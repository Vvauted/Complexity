/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Refinement
import Complexity.Tactic.Ram.Total
import Complexity.Tactic.Ram.Word

/-!
# Verification through ordinary mathematical models

`ram_refine x s hs [definitions, facts]` starts a `Source.Refines` proof:
`x` is the ordinary mathematical input, `s` the concrete entry state and `hs`
its representation assertion. The last argument also accepts a native
`rcases` pattern, such as `⟨hmodel, hbounds⟩`, to name representation facts and
ghost witnesses directly. It then uses the existing budget-free
verification conditions. Calls and loops still use their explicit contracts;
`ram_total_apply (implementation x)` applies a proved refinement as a contract.

`ram_model [representation laws, mathematical facts]` simplifies observations
using the ordinary Lean/mathlib simp interface, then normalizes unsigned word
arithmetic with `ram_word`. It supports the usual `at h` and `at *` locations.
The mathematical model can be any type: no list-specific representation
registry or separate collection theory is introduced. For example, a supplied
equation identifying a memory observation with a finite function, set or list
rewrites arbitrary predicates about that observation in the usual way.

Representation laws must be proved and supplied explicitly (or registered with
Lean's ordinary `simp` attribute). This tactic does not infer a representation,
discard safety conditions or unfold program and compiler definitions on its own.
Unresolved mathematical obligations remain available to ordinary Lean tactics.
Native state computations reuse the upstream `StateT.run_*` simp rules;
unfolding the identity-monad instance exposes their returned pairs so ordinary
model rules can continue simplifying observations of the final state.
-/

open Lean.Parser.Tactic

/-- Start a refinement proof with a mathematical input and its concrete
representation, then generate the existing budget-free verification conditions. -/
syntax (name := ramRefine) "ram_refine " ident ppSpace ident ppSpace rcasesPat
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_refine $x:ident $s:ident $hs:rcasesPat) =>
      `(tactic| ram_refine $x $s $hs [])
  | `(tactic| ram_refine $x:ident $s:ident $hs:rcasesPat [$args,*]) =>
      `(tactic|
        (intro $x:ident
         ram_total_vc $s $hs [$args,*]))

/-- Rewrite observations through supplied model laws using standard mathlib
simplification, then normalize word arithmetic without assuming no overflow. -/
syntax (name := ramModel) "ram_model" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| ram_model $[$loc:location]?) =>
      `(tactic| ram_model [] $[$loc]?)
  | `(tactic| ram_model [$args,*] $[$loc:location]?) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) [Id.instMonad, $args,*] $[$loc]?
         <;> try ram_word [$args,*] $[$loc]?))
