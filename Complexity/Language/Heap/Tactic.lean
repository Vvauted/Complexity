/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap
import Aesop

/-!
# Borrowed-buffer frame consequences

`buffer_frame` closes logical consequences of supplied contents observations,
borrowed-view frames and disjointness facts. Aesop forwards observations through
the actual endpoint heaps and derives the symmetric orientation of an existing
disjointness proof. Its local rules do not affect other invocations of `aesop`.

The tactic performs no array-specific simplification, arithmetic or alias
analysis. Array results and separation conditions must already be supplied;
unresolved mathematical obligations make the tactic fail.
-/

namespace Complexity.Language

/-- Close routine contents and frame consequences after source verification.
Only supplied frames and disjointness facts transport observations; distinct
object identifiers or a globally disjoint heap are not assumed. -/
macro "buffer_frame" : tactic =>
  `(tactic| aesop
    (rule_sets := [-default])
    (add safe forward Buffer.PreservesOutside.contents,
      safe forward Buffer.PreservesOutside.trans, safe forward Buffer.Disjoint.symm)
    (erase Aesop.BuiltinRules.ext, Aesop.BuiltinRules.splitTarget,
      Aesop.BuiltinRules.splitHypotheses)
    (config := {
      terminal := true, enableSimp := false, enableUnfold := false,
      assumptionTransparency := .default, applyHypsTransparency := .reducible }))

end Complexity.Language
