/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Execution.Block.Basic
import Complexity.Computability.Ram.Execution.Memory
import Complexity.Computability.Ram.Execution.Resource
import Init.Data.List.Nat.TakeDrop

/-!
# Every intermediate state of a linear instruction block

The existing `execBlock` transformer agrees with the real machine after every
`take k`, not only after the complete block. This gives a finite, exact view of
`PrefixBound`: all `k ≤ block.length` observations must satisfy the proposed
bound. Checking only the two endpoints does not establish a peak bound.

Heap accesses and writes instead use `k < block.length`, reading each
instruction's operands in its actual entry state. The unexecuted instruction
at the endpoint is excluded. No new runner, resource observation, or footprint
is defined. The existing `Instr.Linear` restriction is unchanged: branches,
jumps, halt, and potentially faulting input reads are not linear instructions.
-/

namespace Ram

/-- A clamped list prefix occupies the same initial code interval. -/
theorem CodeAt.take {code block : Code} {pc : Nat}
    (atBlock : CodeAt code pc block) (k : Nat) : CodeAt code pc (block.take k) := by
  have splitBlock : CodeAt code pc (block.take k ++ block.drop k) := by
    simpa only [List.take_append_drop] using atBlock
  exact splitBlock.append_left

private theorem linear_take {block : Code} (linear : ∀ instr ∈ block, instr.Linear)
    (k : Nat) : ∀ instr ∈ block.take k, instr.Linear :=
  fun instr member => linear instr (List.mem_of_mem_take member)

/-- Every bounded prefix of a running linear block executes in exactly its
length many real machine transitions. -/
theorem execBlock_take_exec {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ instr ∈ block, instr.Linear)
    (running : s.status = .running) {k : Nat} (hk : k ≤ block.length) :
    Exec code k s (execBlock (block.take k) s) := by
  simpa only [List.length_take_of_le hk] using
    execBlock_exec (atBlock.take k) (linear_take linear k) running

/-- Determinism identifies any real prefix endpoint with the corresponding
`execBlock` prefix, so no arbitrary intermediate state needs to be guessed. -/
theorem Exec.eq_execBlock_take {code block : Code} {s t : State w} {k : Nat}
    (execution : Exec code k s t) (atBlock : CodeAt code s.pc block)
    (linear : ∀ instr ∈ block, instr.Linear) (running : s.status = .running)
    (hk : k ≤ block.length) : t = execBlock (block.take k) s :=
  execution.deterministic (execBlock_take_exec atBlock linear running hk)

/-- The full prefix observation bound is exactly the bound at every list
prefix state, including both the initial state and the complete block's result. -/
theorem prefixBound_execBlock_iff {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ instr ∈ block, instr.Linear)
    (running : s.status = .running) (observe : State w → Nat) (bound : Nat) :
    PrefixBound observe code block.length s bound ↔
      ∀ k, k ≤ block.length → observe (execBlock (block.take k) s) ≤ bound := by
  constructor
  · intro h k hk
    exact h k hk _ (execBlock_take_exec atBlock linear running hk)
  · intro h k hk current execution
    rw [execution.eq_execBlock_take atBlock linear running hk]
    exact h k hk

private theorem block_prefix_ready {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ instr ∈ block, instr.Linear)
    (running : s.status = .running) {k : Nat} (hk : k < block.length) :
    (execBlock (block.take k) s).status = .running ∧
      code[(execBlock (block.take k) s).pc]? = some block[k] := by
  refine ⟨(execBlock_status _ s (linear_take linear k)).trans running, ?_⟩
  rw [execBlock_pc _ s (linear_take linear k), List.length_take_of_le (Nat.le_of_lt hk)]
  exact (atBlock k hk).trans (List.getElem?_eq_getElem hk)

/-- A block's cumulative access set consists exactly of the instructions'
accesses evaluated at their real entry states, not at the block's final state. -/
theorem mem_heapAccesses_execBlock_iff {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ instr ∈ block, instr.Linear)
    (running : s.status = .running) (address : Word w) :
    address ∈ heapAccesses code block.length s ↔
      ∃ k, ∃ hk : k < block.length,
        address ∈ block[k].heapAccesses (execBlock (block.take k) s) := by
  constructor
  · intro member
    obtain ⟨k, hk, current, _, execution, _, access⟩ := mem_heapAccesses_iff.mp member
    have endpoint := execution.eq_execBlock_take atBlock linear running (Nat.le_of_lt hk)
    obtain ⟨ready, fetch⟩ := block_prefix_ready atBlock linear running hk
    rw [endpoint, stepHeapAccesses_of_fetch ready fetch] at access
    exact ⟨k, hk, access⟩
  · rintro ⟨k, hk, access⟩
    obtain ⟨ready, fetch⟩ := block_prefix_ready atBlock linear running hk
    exact mem_heapAccesses_iff.mpr ⟨k, hk, _, _,
      execBlock_take_exec atBlock linear running (Nat.le_of_lt hk),
      step_of_fetch ready fetch, by simpa only [stepHeapAccesses_of_fetch ready fetch] using access⟩

/-- The same characterization for actual stores lets the existing memory
frame theorem be applied using the block's list of instructions. -/
theorem mem_heapWrites_execBlock_iff {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ instr ∈ block, instr.Linear)
    (running : s.status = .running) (address : Word w) :
    address ∈ heapWrites code block.length s ↔
      ∃ k, ∃ hk : k < block.length,
        address ∈ block[k].heapWrites (execBlock (block.take k) s) := by
  constructor
  · intro member
    obtain ⟨k, hk, current, _, execution, _, write⟩ := mem_heapWrites_iff.mp member
    have endpoint := execution.eq_execBlock_take atBlock linear running (Nat.le_of_lt hk)
    obtain ⟨ready, fetch⟩ := block_prefix_ready atBlock linear running hk
    rw [endpoint, stepHeapWrites_of_fetch ready fetch] at write
    exact ⟨k, hk, write⟩
  · rintro ⟨k, hk, write⟩
    obtain ⟨ready, fetch⟩ := block_prefix_ready atBlock linear running hk
    exact mem_heapWrites_iff.mpr ⟨k, hk, _, _,
      execBlock_take_exec atBlock linear running (Nat.le_of_lt hk),
      step_of_fetch ready fetch, by simpa only [stepHeapWrites_of_fetch ready fetch] using write⟩

end Ram
