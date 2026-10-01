/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Prod
import Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources

/-!
# Allocation-aware costs of pair-list operations

The actual source bodies construct or read two scalar nodes. The structural
cost rules infer bounds from those bodies, including projections, option tags,
field packing, selected branches and function initialization. A pair cons adds
two three-word nodes; six reserved words are not an instruction count.

The same operations implement signed lists. These conditional cost contracts
are independent of mathematical correctness; caller word ranges, capacity and
arena readiness remain separate requirements.
-/

namespace Ram.LanguageCompiler.List.Prod

open Complexity.Language
open Complexity.Language.List.Prod.Operations

/-- A uniform body budget inferred from the two real allocations and packaging. -/
def consBoolNatBodyCost : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (head : Bool × Nat)
      (tail : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap),
      StmtArenaCostBound program w heapLimit depth (program.body consBoolNatId)
        ⟨consBoolNat_args head tail, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth head tail heap
  change StmtArenaCostBound program w heapLimit depth consBoolNatBody
    ⟨consBoolNat_args head tail, heap⟩ _
  ram_source_arena_cost⟩

/-- The allocating function's bound includes its private initialization once. -/
theorem consBoolNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body consBoolNatId)
      (fun input : (Bool × Nat) × (Option (NodeRef .bool) × Option (NodeRef .nat)) =>
        consBoolNat_args input.1 input.2)
      (fun _ _ => True) w heapLimit depth (fun _ => consBoolNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    consBoolNatBodyCost.property w heapLimit depth input.1 input.2 heap)

/-- The reader's uniform bound charges the selected matches and real reads. -/
def unconsBoolNatBodyCost : { bound : Nat //
    ∀ (w heapLimit depth : Nat)
      (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap),
      StmtArenaCostBound program w heapLimit depth (program.body unconsBoolNatId)
        ⟨unconsBoolNat_args roots, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth roots heap
  change StmtArenaCostBound program w heapLimit depth unconsBoolNatBody
    ⟨unconsBoolNat_args roots, heap⟩ _
  ram_source_arena_cost⟩

/-- The same source reader retains real function initialization in its budget. -/
theorem unconsBoolNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body unconsBoolNatId)
      unconsBoolNat_args (fun _ _ => True) w heapLimit depth
      (fun _ => unconsBoolNatBodyCost.val + 2) :=
  FunctionArenaCostBound.of_stmt (fun roots heap _ =>
    unconsBoolNatBodyCost.property w heapLimit depth roots heap)

end Ram.LanguageCompiler.List.Prod
