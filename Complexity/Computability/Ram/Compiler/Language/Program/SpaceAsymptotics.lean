/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Asymptotics

/-!
# Asymptotic arithmetic for established program space bounds

`program_space_asymptotics [leaf, one, ...]` reuses the existing mathematical
`IsBigO` composition engine. It handles natural-number addition, maxima,
successors and fixed multiplication, including word-to-byte factors and fixed
frame sizes. Expose the selected space envelope with ordinary `unfold` first.
Supply its asymptotic leaves and a `1 =O growth` proof when constants occur.

This entry composes arithmetic only. It does not establish that an expression
measures the same execution's space, infer an initial footprint, discharge
capacity, or turn retained/cumulative allocation into peak-live storage. An
execution-space certificate must justify the envelope separately. In particular,
the arithmetic `max` rule does not assert that sequential address unions combine
by maximum. Input, metadata and stack accounting are not erased by this tactic.

The shared engine also recognizes the existing time-overhead expressions
`callCost` and `invocationBound`. Its rules for them remain valid numerical
`IsBigO` statements, not evidence that those instruction counts price space.
No source bodies or fixed operation metadata are unfolded, no new resource
semantics is introduced, and unsupported mathematical leaves remain goals.
-/

syntax "program_space_asymptotics" "[" term,* "]" : tactic

macro_rules
  | `(tactic| program_space_asymptotics [$certificates:term,*]) =>
      `(tactic| program_time_asymptotics [$certificates:term,*])
