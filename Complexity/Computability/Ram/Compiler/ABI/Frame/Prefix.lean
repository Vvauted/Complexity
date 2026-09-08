/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Frame.Memory
import Complexity.Computability.Ram.Execution.MemoryBounds

/-!
# Source-heap preservation throughout actual frame operations

The exact write sets of frame saves imply that every real intermediate state
preserves the source heap. A restore has no stores at all, so every prefix
preserves the entire memory. These conclusions are stronger than the existing
endpoint frame results: no temporary source-heap write is permitted.

The base in every statement is the SP at that block's actual entry. Applying
these rules inside calls still requires the caller's save entry or the
post-retreat restore entry, rather than an arbitrary instantaneous SP.
-/

namespace Ram.ABI

/-- Saving the return address never modifies source-visible heap words,
including during the intermediate register-setup instruction. -/
theorem saveReturn_prefix_heap {code : Code} {control returnPC limit k : Nat}
    {start current : State w}
    (atBlock : CodeAt code start.pc (saveReturn control returnPC))
    (running : start.status = .running) (heap : limit ≤ (start.regs (sp control)).toNat)
    (hk : k ≤ 2) (execution : Exec code k start current) :
    HeapEqBelow limit start.mem current.mem := by
  apply execution.prefix_heapEqBelow_of_writes_above hk limit
  intro address member
  rw [saveReturn_heapWrites atBlock running, Finset.mem_singleton] at member
  simpa only [member] using heap

/-- All source-heap words remain intact throughout saving local slots. No
local-register bound is needed for this write-address statement; a no-wrap
bound separates the actual modular slot addresses from the source heap. -/
theorem saveLocals_prefix_heap {code : Code} {control count limit k : Nat}
    {start current : State w}
    (atBlock : CodeAt code start.pc (saveLocals control count))
    (running : start.status = .running) (heap : limit ≤ (start.regs (sp control)).toNat)
    (fits : (start.regs (sp control)).toNat + count < 2 ^ w)
    (hk : k ≤ 3 * count) (execution : Exec code k start current) :
    HeapEqBelow limit start.mem current.mem := by
  apply execution.prefix_heapEqBelow_of_writes_above hk limit
  intro address member
  rw [saveLocals_heapWrites atBlock running] at member
  exact heap.trans (mem_slot_image_iff fits |>.mp member).1.le

/-- Restoring a local performs no memory write, even if its destination is
outside the ordinary local-register range. Every real prefix is write-free. -/
theorem restoreLocal_prefix_mem {code : Code} {control slot k : Nat}
    {start current : State w}
    (atBlock : CodeAt code start.pc (restoreLocal control slot))
    (running : start.status = .running) (hk : k ≤ 3)
    (execution : Exec code k start current) : current.mem = start.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk (restoreLocal_heapWrites atBlock running)

/-- Every prefix of a batch restore preserves the entire memory. Unlike its
entry-SP read-set formula, this needs no bound on the restored register count. -/
theorem restoreLocals_prefix_mem {code : Code} {control count k : Nat}
    {start current : State w}
    (atBlock : CodeAt code start.pc (restoreLocals control count))
    (running : start.status = .running) (hk : k ≤ 3 * count)
    (execution : Exec code k start current) : current.mem = start.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk (restoreLocals_heapWrites atBlock running)

end Ram.ABI
