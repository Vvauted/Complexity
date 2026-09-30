/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.GetD
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.FixedHeap

/-!
# Constant costs for defaulted array lookup

The existing source functions check the buffer length and read only in bounds.
Their budgets below are inferred from the actual primitive, branch, read and
return rules. They neither assign a new price to lookup nor establish successful
execution: correctness and word-range readiness remain separate contracts.

Both bodies are local and nonallocating, so the existing same-execution bridge
also supplies their conditional arena bounds. Function initialization is counted
once; a caller still pays its ordinary call overhead.
-/

namespace Ram.LanguageCompiler.Buffer.GetD

open Complexity.Language
open Complexity.Language.Buffer.GetD

/-- An input-independent bound inferred from the natural lookup's actual body. -/
def getNatBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State [.buffer .nat, .nat, .nat],
      StmtCostBound program (program.body getNatId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getNatBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.read_uniform
    intro value
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- Boolean lookup pays for its own bounds check, selected branch and read. -/
def getBoolBodyCost : { bound : Nat //
    ∀ initial : Complexity.Language.State [.buffer .bool, .nat, .bool],
      StmtCostBound program (program.body getBoolId) initial bound } := ⟨_, by
  intro initial
  change StmtCostBound program getBoolBody initial _
  apply StmtCostBound.letPrim
  apply StmtCostBound.letPrim
  apply StmtCostBound.ite_max
  · apply StmtCostBound.read_uniform
    intro value
    exact StmtCostBound.ret _ _
  · exact StmtCostBound.ret _ _⟩

/-- Natural lookup includes the compiler's function initialization once. -/
theorem getNat_costBound :
    FunctionCostBound program getNatId (fun _ _ => True)
      (fun _ _ => getNatBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getNatBodyCost.property ⟨args, heap⟩)

/-- Boolean lookup includes the same existing function-wrapper charge. -/
theorem getBool_costBound :
    FunctionCostBound program getBoolId (fun _ _ => True)
      (fun _ _ => getBoolBodyCost.val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => getBoolBodyCost.property ⟨args, heap⟩)

/-- The natural lookup has no allocation, reclaiming scope or nested call. -/
theorem getNat_noAllocationOrCalls : NoAllocationOrCalls (program.body getNatId) := by
  change NoAllocationOrCalls getNatBody
  simp [getNatBody, NoAllocationOrCalls]

/-- The Boolean lookup has no allocation, reclaiming scope or nested call. -/
theorem getBool_noAllocationOrCalls : NoAllocationOrCalls (program.body getBoolId) := by
  change NoAllocationOrCalls getBoolBody
  simp [getBoolBody, NoAllocationOrCalls]

/-- The existing local-body bridge retains the same natural lookup cost in an
allocating caller; this implication assumes that caller's actual readiness. -/
theorem getNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getNatId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls getNat_costBound getNat_noAllocationOrCalls

/-- Boolean lookup inherits its arena bound without re-pricing any operation. -/
theorem getBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body getBoolId) id (fun _ _ => True)
      w heapLimit depth (fun _ => getBoolBodyCost.val + 2) :=
  FunctionArenaCostBound.of_noAllocationOrCalls getBool_costBound getBool_noAllocationOrCalls

end Ram.LanguageCompiler.Buffer.GetD
