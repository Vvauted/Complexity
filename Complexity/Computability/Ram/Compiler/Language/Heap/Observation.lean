/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap

/-!
# Shared heap representations on actual RAM data

`Source.State.ofRam` forgets only the machine's program counter and status. It
retains every register and memory word, including private stack memory, together
with the actual input and output. This is a mathematical projection, not an
execution step, memory copy or initialization operation.

`HeapRep.of_observes` transfers a represented source heap to this projection of
the actual machine state. A later invocation can therefore retain all physical
memory from the previous invocation while reusing its proved heap representation.
Only represented object cells require agreement; no assertion is made that
compiler-private memory agrees with a source execution witness.
-/

namespace Ram.Source.State

variable {w : Nat}

/-- Retain all actual machine data, forgetting only execution control fields. -/
def ofRam (target : Ram.State w) : Source.State w where
  regs := target.regs
  mem := target.mem
  input := target.input
  outputRev := target.outputRev

@[simp]
theorem ofRam_regs (target : Ram.State w) : (ofRam target).regs = target.regs := rfl

@[simp]
theorem ofRam_mem (target : Ram.State w) : (ofRam target).mem = target.mem := rfl

@[simp]
theorem ofRam_input (target : Ram.State w) : (ofRam target).input = target.input := rfl

@[simp]
theorem ofRam_outputRev (target : Ram.State w) :
    (ofRam target).outputRev = target.outputRev := rfl

/-- The full data projection observes the actual state at every chosen boundary. -/
theorem ofRam_observes (target : Ram.State w) (heapLimit locals : Nat) :
    Observes heapLimit locals (ofRam target) target :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

end Ram.Source.State

namespace Ram.LanguageCompiler.HeapRep

open Complexity.Language

variable {w heapLimit : Nat} {placement : Nat → Word w} {heap : Heap}

/-- A heap representation depends only on actual memory below its boundary.
Registers, I/O and memory outside that boundary need not agree. -/
theorem of_heapEqBelow {source next : Source.State w}
    (represented : HeapRep placement heapLimit heap source)
    (equal : HeapEqBelow heapLimit source.mem next.mem) :
    HeapRep placement heapLimit heap next := by
  refine ⟨?_, represented.fit, represented.disjoint, represented.backward⟩
  intro object stored found
  have current := represented.stored found
  refine ⟨⟨current.1.fits, ?_⟩, current.2⟩
  intro index bound
  exact (equal _ (current.addr_lt bound)).symm.trans (current.1.lookup index bound)

/-- The actual completed machine data retains the represented source heap,
including when its private stack words differ from the source witness. -/
theorem of_observes {locals : Nat} {source : Source.State w} {target : Ram.State w}
    (represented : HeapRep placement heapLimit heap source)
    (observed : Source.State.Observes heapLimit locals source target) :
    HeapRep placement heapLimit heap (Source.State.ofRam target) :=
  represented.of_heapEqBelow observed.heap

end Ram.LanguageCompiler.HeapRep
