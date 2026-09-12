/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Heap.Tactic
import Std.Tactic.Do.Syntax

/-!
# Composing supplied native source specifications

`source_vc [spec₁, spec₂]` composes explicit `Std.Do.Triple` specifications and
the standard return rule. Each specification is a separate local Aesop rule,
so another applicable contract remains available if an earlier choice cannot
discharge its precondition. `mspec` handles the actual bind and call, `mleave`
exposes its logical obligations, and `buffer_frame` closes supplied frame
consequences at the actual intermediate heaps.

Beyond the standard `Triple`/WP logical conversions, only environment head/tail
projections are simplified. The tactic does not unfold caller or callee bodies,
infer array results or introduce separation assumptions. Unprovided
specifications and unresolved mathematics cause failure.
-/

namespace Complexity.Language

open Lean

/-- Compose explicit native contracts, preserving alternatives for backtracking.
Unfold the caller's public equation before invoking this tactic; callees remain
abstract behind their supplied specifications. -/
macro "source_vc" " [" specifications:term,* "]" : tactic => do
  let specifications := specifications.getElems
  let rules ← specifications.mapM fun specification =>
    `(Aesop.rule_expr| unsafe 90% (by
      mspec $specification
      all_goals try mleave))
  let rules := rules ++ #[
    ← `(Aesop.rule_expr| unsafe 90% (by
      mspec Std.Do.Spec.pure
      all_goals try mleave)),
    ← `(Aesop.rule_expr| safe (by buffer_frame)),
    ← `(Aesop.rule_expr| norm simp Env.head_cons),
    ← `(Aesop.rule_expr| norm simp Env.tail_cons)]
  `(tactic| (
    try simp only [Std.Do.Triple]
    mleave
    all_goals
      aesop
        (rule_sets := [-default])
        (add $rules:Aesop.rule_expr,*)
        (erase Aesop.BuiltinRules.ext, Aesop.BuiltinRules.splitTarget,
          Aesop.BuiltinRules.splitHypotheses)
        (config := {
          terminal := true, useDefaultSimpSet := false, enableUnfold := false,
          assumptionTransparency := .default, applyHypsTransparency := .reducible })))

end Complexity.Language
