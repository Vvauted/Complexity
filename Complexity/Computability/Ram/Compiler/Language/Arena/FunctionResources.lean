/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Linking

/-!
# Reusable resource contracts for actual source function bodies

An index selects the actual arguments and their mathematical precondition at
the entry heap. It may contain both a mathematical value and a concrete source
value related to it: shared heap representations need not have a unique encoder.
The selected body is real source code, not a mathematical callback.

Readiness and instruction bounds observe the same existing `Exec`, `ArenaReady`
and `ArenaExecutionCost`. They do not supply termination. The reserved amount
bounds retained cursor growth and supplies capacity for the readiness proof;
it is not exact peak live space. The body bound includes its two initialization
instructions, while call-frame work and outer halt are charged by the caller.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- Conditional finite-word and arena readiness for the specified actual body.
The mathematical index can retain representation witnesses without treating
their decoding as runtime work. -/
def FunctionArenaResources {X : Type u} {signatures : List Signature}
    (program : Complexity.Language.Program signatures) {Γ : List Ty} {result : Ty}
    (body : Complexity.Language.Stmt signatures Γ result)
    (args : X → Env Γ) (pre : X → Heap → Prop)
    (w heapLimit depth : Nat) (reserve : X → Nat) : Prop :=
  ∀ x heap cursor, pre x heap → EnvFits w (args x) →
    cursor + reserve x ≤ heapLimit → ∀ finish value,
      ∀ execution : Complexity.Language.Exec program body ⟨args x, heap⟩ finish (.returned value),
        ∃ finalCursor, ∃ _ready : ArenaReady execution w heapLimit depth cursor finalCursor,
          finalCursor ≤ cursor + reserve x

/-- A separate bound on the existing compiler cost of that same function body.
Body initialization is included exactly once, as in `FunctionCostBound`.
Neither a proposed bound nor this predicate can establish source termination. -/
def FunctionArenaCostBound {X : Type u} {signatures : List Signature}
    (program : Complexity.Language.Program signatures) {Γ : List Ty} {result : Ty}
    (body : Complexity.Language.Stmt signatures Γ result)
    (args : X → Env Γ) (pre : X → Heap → Prop)
    (w heapLimit depth : Nat) (bound : X → Nat) : Prop :=
  ∀ x heap, pre x heap → ∀ finish value,
    ∀ execution : Complexity.Language.Exec program body ⟨args x, heap⟩ finish (.returned value),
      ∀ {cursor finalCursor} (ready : ArenaReady execution w heapLimit depth cursor finalCursor)
        {steps}, ArenaExecutionCost ready steps → steps + 2 ≤ bound x

/-- Relocation preserves the actual body's readiness and retained arena bound.
Argument values and their heap-indexed precondition are unchanged. -/
theorem FunctionArenaResources.renameCalls {X : Type u} {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    {Γ : List Ty} {result : Ty} {body : Complexity.Language.Stmt source Γ result}
    {args : X → Env Γ} {pre : X → Heap → Prop}
    {w heapLimit depth : Nat} {reserve : X → Nat}
    (resources : FunctionArenaResources sourceProgram body args pre w heapLimit depth reserve)
    (embedded : sourceProgram.Embeds map targetProgram) :
    FunctionArenaResources targetProgram (body.renameCalls map) args pre
      w heapLimit depth reserve := by
  intro x heap cursor allowed fits capacity finish value execution
  obtain ⟨finalCursor, ready, bound⟩ :=
    resources x heap cursor allowed fits capacity finish value (execution.of_renameCalls embedded)
  exact ⟨finalCursor, ready.renameCalls embedded, bound⟩

/-- A linked invocation has the same compiler count, including its actual
recursive callees; the mathematical bound is transported without repricing. -/
theorem FunctionArenaCostBound.renameCalls {X : Type u} {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    {Γ : List Ty} {result : Ty} {body : Complexity.Language.Stmt source Γ result}
    {args : X → Env Γ} {pre : X → Heap → Prop}
    {w heapLimit depth : Nat} {bound : X → Nat}
    (bounded : FunctionArenaCostBound sourceProgram body args pre w heapLimit depth bound)
    (embedded : sourceProgram.Embeds map targetProgram) :
    FunctionArenaCostBound targetProgram (body.renameCalls map) args pre
      w heapLimit depth bound := by
  intro x heap allowed finish value execution cursor finalCursor ready steps cost
  exact bounded x heap allowed finish value (execution.of_renameCalls embedded)
    (ready.of_renameCalls embedded) (cost.of_renameCalls embedded)

end Ram.LanguageCompiler
