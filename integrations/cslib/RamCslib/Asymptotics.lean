/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity

/-!
# Compatibility import for RAM's mathlib asymptotic API

The main library now directly uses mathlib's `Asymptotics.IsBigO` for actual
uniform RAM runtime witnesses. `UniformTimeBound.bigO_of_isBigO` is provided by
`Ram.Complexity`; this module preserves the previous import path without
maintaining a second definition or proof.
-/
