/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.MergeSort.Time
import Complexity.Computability.Ram.Verification.Recursion.Time

/-!
# Recursive contract for the actual RAM merge-sort function

The public measured contract combines independent functional recursion and
actual-time proofs. Initialization, both recursive calls and merge/copy-back
retain their original implementation, bounds and two-buffer frame. Functional
clients use `recursive_total` without choosing or threading unused time.
-/

namespace Ram.Source.Array.MergeSort

variable {w control heapLimit selfFn : Nat} {functions : Program}

/-- The fixed function terminates on every represented array. Its ghost
recursion argument is the list, ordered only by length; neither the budget nor
the mathematical sorting operation is an executable instruction. -/
theorem recursive_contract (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    ∀ xs, (recursionSpec heapLimit selfFn w).Correct control functions heapLimit xs :=
  fun xs => (recursive_total hw lookup xs).with_timeBound
    (recursive_timeBound (control := control) hw lookup xs)

/-- The public preloaded-array body contract retains the final sorted array,
scratch allocation, outside-memory frame, and both I/O observations. -/
theorem body_contract {base scratch : Word w} {xs : List (Word w)}
    (hw : 2 ≤ w) (lookup : functions[selfFn]? = some (function selfFn)) :
    RelContract control functions heapLimit (Nat.clog 2 xs.length) (function selfFn).body
      (Pre heapLimit base scratch xs) (Post heapLimit base scratch xs)
      (fun _ => budget xs.length) := by
  intro entry hp
  have specPre : (recursionSpec heapLimit selfFn w).pre xs entry := by
    change Pre heapLimit (entry.regs 0) (entry.regs 1) xs entry
    simpa only [hp.base_reg, hp.scratch_reg] using hp
  obtain ⟨steps, finish, execution, ⟨_, post⟩, bounded⟩ :=
    recursive_contract (control := control) hw lookup xs entry specPre
  refine ⟨steps, finish, execution, ?_, bounded⟩
  change Post heapLimit (entry.regs 0) (entry.regs 1) xs entry finish at post
  simpa only [hp.base_reg, hp.scratch_reg] using post

end Ram.Source.Array.MergeSort
