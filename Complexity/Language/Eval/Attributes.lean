/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The native source-action simplification attribute

Lean initializes a registered simp attribute when this module is imported.
`Eval.Simp` supplies its primitive equations without changing the global simp set.
-/

namespace Complexity.Language

/-- Native monad administration and the existing primitive heap actions.
Use explicitly with `simp [source_eval, ...]` after opening the desired source
equation; branch conditions and actual call/access facts remain local inputs. -/
register_simp_attr source_eval

end Complexity.Language
