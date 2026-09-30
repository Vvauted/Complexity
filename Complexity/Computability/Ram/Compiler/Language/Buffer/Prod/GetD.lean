/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Prod.GetD
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap

/-!
# Compiled costs for defaulted scalar-pair reads

Each budget follows the source body's actual projections, length test, branch,
two in-bounds reads and pure pair construction. The out-of-bounds branch returns
the existing fallback pair without reading either column. The uniform bound
uses the larger branch; it does not execute or sum both alternatives.

Function initialization is included once. Successful execution and RAM
readiness remain separate premises; these inferred budgets do not provide
input loading, word-range certificates or a new operation price.
-/

namespace Ram.LanguageCompiler.Buffer.Prod.GetD

open Complexity.Language
open Complexity.Language.Buffer.Prod.GetD

/-- An input-independent budget inferred from this entry's actual source body. -/
def getNatNatBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .nat) (.buffer .nat), .nat, .prod .nat .nat],
      StmtCostBound program (program.body getNatNatId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getNatNatBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.read_uniform
    intro second
    apply StmtCostBound.letPrim
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- The existing function-wrapper rule includes initialization exactly once. -/
theorem getNatNat_costBound :
    FunctionCostBound program getNatNatId (fun _ _ => True)
      (fun _ _ => getNatNatBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getNatNatBodyCost.property ⟨args, heap⟩)

/-- Both branches use only nonallocating local instructions. -/
theorem getNatNat_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getNatNatId) := by
  change NoAllocationOrCalls getNatNatBody
  simp [getNatNatBody, NoAllocationOrCalls]

/-- The same body budget applies in an allocating caller with explicit readiness. -/
theorem getNatNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getNatNatId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getNatNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getNatNat_costBound getNatNat_noAllocationOrCalls

/-- An input-independent budget inferred from this entry's actual source body. -/
def getNatBoolBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .nat) (.buffer .bool), .nat, .prod .nat .bool],
      StmtCostBound program (program.body getNatBoolId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getNatBoolBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.read_uniform
    intro second
    apply StmtCostBound.letPrim
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- The existing function-wrapper rule includes initialization exactly once. -/
theorem getNatBool_costBound :
    FunctionCostBound program getNatBoolId (fun _ _ => True)
      (fun _ _ => getNatBoolBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getNatBoolBodyCost.property ⟨args, heap⟩)

/-- Both branches use only nonallocating local instructions. -/
theorem getNatBool_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getNatBoolId) := by
  change NoAllocationOrCalls getNatBoolBody
  simp [getNatBoolBody, NoAllocationOrCalls]

/-- The same body budget applies in an allocating caller with explicit readiness. -/
theorem getNatBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getNatBoolId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getNatBoolBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getNatBool_costBound getNatBool_noAllocationOrCalls

/-- An input-independent budget inferred from this entry's actual source body. -/
def getBoolNatBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .bool) (.buffer .nat), .nat, .prod .bool .nat],
      StmtCostBound program (program.body getBoolNatId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getBoolNatBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.read_uniform
    intro second
    apply StmtCostBound.letPrim
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- The existing function-wrapper rule includes initialization exactly once. -/
theorem getBoolNat_costBound :
    FunctionCostBound program getBoolNatId (fun _ _ => True)
      (fun _ _ => getBoolNatBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getBoolNatBodyCost.property ⟨args, heap⟩)

/-- Both branches use only nonallocating local instructions. -/
theorem getBoolNat_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getBoolNatId) := by
  change NoAllocationOrCalls getBoolNatBody
  simp [getBoolNatBody, NoAllocationOrCalls]

/-- The same body budget applies in an allocating caller with explicit readiness. -/
theorem getBoolNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getBoolNatId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getBoolNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getBoolNat_costBound getBoolNat_noAllocationOrCalls

/-- An input-independent budget inferred from this entry's actual source body. -/
def getBoolBoolBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State
      [.prod (.buffer .bool) (.buffer .bool), .nat, .prod .bool .bool],
      StmtCostBound program (program.body getBoolBoolId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getBoolBoolBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.letPrim
    apply StmtCostBound.read_uniform
    intro first
    apply StmtCostBound.read_uniform
    intro second
    apply StmtCostBound.letPrim
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- The existing function-wrapper rule includes initialization exactly once. -/
theorem getBoolBool_costBound :
    FunctionCostBound program getBoolBoolId (fun _ _ => True)
      (fun _ _ => getBoolBoolBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getBoolBoolBodyCost.property ⟨args, heap⟩)

/-- Both branches use only nonallocating local instructions. -/
theorem getBoolBool_noAllocationOrCalls :
    NoAllocationOrCalls (program.body getBoolBoolId) := by
  change NoAllocationOrCalls getBoolBoolBody
  simp [getBoolBoolBody, NoAllocationOrCalls]

/-- The same body budget applies in an allocating caller with explicit readiness. -/
theorem getBoolBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getBoolBoolId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getBoolBoolBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls
    getBoolBool_costBound getBoolBool_noAllocationOrCalls

end Ram.LanguageCompiler.Buffer.Prod.GetD
