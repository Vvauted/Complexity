/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Replicate
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Allocation

/-!
# Allocation-aware costs of scalar array replication

The body budgets are inferred from the existing initialized-allocation and
return rules for the actual source bodies. Function initialization is included
once. These conditional costs retain the supplied execution and arena readiness;
they do not supply capacity, scalar word bounds or a different allocator.
-/

namespace Ram.LanguageCompiler.Buffer.Replicate

open Complexity.Language
open Complexity.Language.Buffer.Replicate

/-- The natural replication body's budget follows actual allocation and return. -/
def replicateNatBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth initial : Nat) (heap : Heap),
      StmtArenaCostBound program w heapLimit depth (program.body replicateNatId)
        ⟨replicateNat_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit depth replicateNatBody
    ⟨replicateNat_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · apply StmtArenaCostBound.alloc
    exact StmtArenaCostBound.ret _ _
  · simp only [replicateNat_args, Atom.eval, Env.cons_here]
    exact Nat.le_refl _⟩

/-- The Boolean body uses the same compiler allocation rule and its real return. -/
def replicateBoolBodyCost (length : Nat) : { bound : Nat //
    ∀ (w heapLimit depth : Nat) (initial : Bool) (heap : Heap),
      StmtArenaCostBound program w heapLimit depth (program.body replicateBoolId)
        ⟨replicateBool_args length initial, heap⟩ bound } := ⟨_, by
  intro w heapLimit depth initial heap
  change StmtArenaCostBound program w heapLimit depth replicateBoolBody
    ⟨replicateBool_args length initial, heap⟩ _
  apply StmtArenaCostBound.mono
  · apply StmtArenaCostBound.alloc
    exact StmtArenaCostBound.ret _ _
  · simp only [replicateBool_args, Atom.eval, Env.cons_here]
    exact Nat.le_refl _⟩

/-- The inferred natural budget is affine in the initialized length, including zero. -/
theorem replicateNatBodyCost_linear (length : Nat) :
    (replicateNatBodyCost length).val = 14 * length + (replicateNatBodyCost 0).val := by
  simp [replicateNatBodyCost, Nat.add_assoc]

/-- Boolean initialization has the same compiler-derived linear coefficient. -/
theorem replicateBoolBodyCost_linear (length : Nat) :
    (replicateBoolBodyCost length).val = 14 * length + (replicateBoolBodyCost 0).val := by
  simp [replicateBoolBodyCost, Nat.add_assoc]

/-- Bound the same callable natural allocator, with function initialization once. -/
theorem replicateNat_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateNatId)
      (fun input : Nat × Nat => replicateNat_args input.1 input.2)
      (fun _ _ => True) w heapLimit depth
      (fun input => (replicateNatBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateNatBodyCost input.1).property w heapLimit depth input.2 heap)

/-- Bound the same callable Boolean allocator with its actual initialized heap. -/
theorem replicateBool_arenaCostBound (w heapLimit depth : Nat) :
    FunctionArenaCostBound program (program.body replicateBoolId)
      (fun input : Nat × Bool => replicateBool_args input.1 input.2)
      (fun _ _ => True) w heapLimit depth
      (fun input => (replicateBoolBodyCost input.1).val + 2) :=
  FunctionArenaCostBound.of_stmt (fun input heap _ =>
    (replicateBoolBodyCost input.1).property w heapLimit depth input.2 heap)

end Ram.LanguageCompiler.Buffer.Replicate
