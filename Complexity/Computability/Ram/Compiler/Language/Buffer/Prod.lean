/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prod
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap

/-!
# Compiled costs for reading scalar-pair arrays

The bound counts the existing compiler's two handle projections, two actual
cell reads, pair construction and return. Function initialization is included
once. These are bounds for the same source body, conditional on RAM readiness;
they do not grant successful execution or hide input loading.
-/

namespace Ram.LanguageCompiler.Buffer.Prod

open Complexity.Language
open Complexity.Language.Buffer.Prod

/-- Infer the fixed read budget from the actual typed source instructions. -/
def readBodyCost (left right : CellTy) : { bound : Nat //
    ∀ initial : Complexity.Language.State (params left right),
      StmtCostBound (program left right) (readBody left right) initial bound } := ⟨_, by
  intro initial
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.read_uniform
  intro first
  apply StmtCostBound.read_uniform
  intro second
  apply StmtCostBound.letPrim
  exact StmtCostBound.ret _ _⟩

/-- The actual function wrapper is charged once, in addition to its body. -/
theorem read_costBound (left right : CellTy) :
    FunctionCostBound (program left right) (readId left right) (fun _ _ => True)
      (fun _ _ => (readBodyCost left right).val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ =>
    (readBodyCost left right).property ⟨args, heap⟩)

/-- Pair reads use only local, nonallocating instructions. -/
theorem read_noAllocationOrCalls (left right : CellTy) :
    NoAllocationOrCalls ((program left right).body (readId left right)) := by
  change NoAllocationOrCalls (readBody left right)
  simp [readBody, NoAllocationOrCalls]

/-- The established local-body bridge retains the same cost in an allocating
caller, with that execution's readiness premises still explicit. -/
theorem read_arenaCostBound (left right : CellTy) (w heapLimit depth : Nat) :
    FunctionArenaCostBound (program left right)
      ((program left right).body (readId left right)) id (fun _ _ => True)
      w heapLimit depth (fun _ => (readBodyCost left right).val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    (read_costBound left right) (read_noAllocationOrCalls left right)

end Ram.LanguageCompiler.Buffer.Prod
