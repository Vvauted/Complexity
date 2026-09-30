/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Ragged.GetD
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap

/-!
# Compiled costs for nested-array row reads

The bound follows the emitted projections, length arithmetic, branch, two
boundary reads and checked slice. It is independent of the row length: no
payload is copied. These are conditional costs of actual successful execution;
RAM readiness and the containing program's allocation remain separate.
-/

namespace Ram.LanguageCompiler.Buffer.Ragged.GetD

open Complexity.Language
open Complexity.Language.Buffer.Ragged.GetD

/-- Infer a uniform budget from the actual row lookup body. -/
def getNatBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .nat) (.buffer .nat), .nat, .buffer .nat],
      StmtCostBound program (program.body getNatId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getNatBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro last
    apply StmtCostBound.letPrim
    apply StmtCostBound.slice_uniform
    intro row
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- Include the existing function initialization rule exactly once. -/
theorem getNat_costBound :
    FunctionCostBound program getNatId (fun _ _ => True)
      (fun _ _ => getNatBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getNatBodyCost.property ⟨args, heap⟩)

/-- Row lookup does not allocate, copy, write, or make hidden calls. -/
theorem getNat_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getNatId) := by
  change NoAllocationOrCalls getNatBody
  simp [getNatBody, NoAllocationOrCalls]

/-- The same body budget composes into an arena caller with explicit readiness. -/
theorem getNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getNatId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getNat_costBound getNat_noAllocationOrCalls

/-- Infer a uniform budget from the actual row lookup body. -/
def getBoolBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .nat) (.buffer .bool), .nat, .buffer .bool],
      StmtCostBound program (program.body getBoolId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getBoolBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro last
    apply StmtCostBound.letPrim
    apply StmtCostBound.slice_uniform
    intro row
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- Include the existing function initialization rule exactly once. -/
theorem getBool_costBound :
    FunctionCostBound program getBoolId (fun _ _ => True)
      (fun _ _ => getBoolBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getBoolBodyCost.property ⟨args, heap⟩)

/-- Row lookup does not allocate, copy, write, or make hidden calls. -/
theorem getBool_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getBoolId) := by
  change NoAllocationOrCalls getBoolBody
  simp [getBoolBody, NoAllocationOrCalls]

/-- The same body budget composes into an arena caller with explicit readiness. -/
theorem getBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getBoolId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getBoolBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getBool_costBound getBool_noAllocationOrCalls

end Ram.LanguageCompiler.Buffer.Ragged.GetD
