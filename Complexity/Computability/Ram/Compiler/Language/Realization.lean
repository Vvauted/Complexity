/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization.Function
import Complexity.Computability.Ram.Compiler.Language.Realization.LocalReturn
import Complexity.Computability.Ram.Compiler.Language.Realization.Loop

/-!
# Source-level realization conditions for the word backend

This module collects the realized execution relation, structural WP rules,
function contracts and loop rules. `Realization.Basic` defines the range/depth
judgment; `Realization.WP`, `Realization.Function`, `Realization.LocalReturn`
and `Realization.Loop` provide its proof interfaces.

These conditions retain the independent source execution and its actual heap.
They contain no target register assignment or proposed instruction budget.
Physical placement and addresses belong to simulation. Finite-fragment lifting
and encoded ranges are available separately from `Realization.Finite` and
`Realization.Range`.
-/
