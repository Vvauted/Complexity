/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Node
import Complexity.Computability.Ram.Memory.Arena.Node

/-!
# Measured allocation of a represented immutable node

The actual straight-line allocator loads the shared cursor, reserves three
words and stores the supplied head, tail tag and placed tail address. The
same final state supplies `ArenaRep.cons_of_rooted`: retaining the tail's
existing identity suffices for the machine bridge. A separate list specialization
adds ordinary mathematical contents to that same allocation.

The three input words are already in registers. Only the fresh-base register
must differ from those inputs; the inputs may alias each other. This boundary
returns one actual base address and excludes operand materialization, packaging
an outer optional root, and function-call setup. Its exact instruction count
comes from the existing compiler's straight-line size, not an assigned price.
-/

namespace Ram.LanguageCompiler.ArenaRep

open Complexity.Language

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Heap} {entry : Source.State w}

/-- One measured execution allocates the real three-word node and returns its
placed address. Its optional tail need only name an existing object: this does
not assert that the tail denotes a correctly typed node or finite list. The
runtime postcondition retains the exact cursor, words and memory/register/I/O frames. -/
theorem cons_measured_of_rooted {program : Ram.Program} {control depth : Nat}
    (registers : Source.Arena.Node.Registers)
    (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (rooted : ValueRooted heap (τ := .option (.node τ)) tail)
    (headFits : cellToNat head < 2 ^ w)
    (capacity : next + 3 ≤ heapLimit)
    (headReg : entry.regs registers.head = cellWord w head)
    (tagReg : entry.regs registers.tag = (if tail.isSome then 1 else 0))
    (tailReg : entry.regs registers.tail = tail.elim 0 (fun ref => placement ref.object)) :
    ∃ finish, Source.LocalMeasuredExec control program heapLimit depth registers.allocate
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) registers.allocate)
        entry finish ∧
      registers.Post heapLimit (BitVec.ofNat w next) (cellWord w head)
        (if tail.isSome then 1 else 0) (tail.elim 0 (fun ref => placement ref.object))
        entry finish ∧
      ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
        (next + 3) heapLimit (heap.cons head tail).2 finish ∧
      finish.regs registers.base =
        (Function.update placement heap.objects.size (BitVec.ofNat w next))
          (heap.cons head tail).1.object := by
  have exactBase : (BitVec.ofNat w next).toNat = next :=
    Word.ofNat_toNat_of_lt (lt_of_le_of_lt arena.cursor_le arena.limit_lt)
  have pre : registers.Pre heapLimit (BitVec.ofNat w next) (cellWord w head)
      (if tail.isSome then 1 else 0) (tail.elim 0 (fun ref => placement ref.object)) entry := {
    cursor := arena.cursor_eq
    head_reg := headReg
    tag_reg := tagReg
    tail_reg := tailReg
    positive := by simpa only [exactBase] using arena.cursor_pos
    capacity := by simpa only [exactBase] using capacity
    fits := arena.limit_lt }
  obtain ⟨finish, execution, post⟩ :=
    registers.allocate_measured (program := program) (control := control) (depth := depth) pre
  have cursor : finish.mem 0 = BitVec.ofNat w (next + 3) := by
    simpa only [arrayAddr, BitVec.ofNat_add_ofNat] using post.cursor
  have initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (heapObjectWords placement (.node τ head tail)).toList finish := by
    cases tail <;> simpa [heapObjectWords] using post.array
  have frame : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address := by
    intro address positive below
    apply post.frame address
    · intro zero
      simp [zero] at positive
    · exact Or.inl (by simpa only [exactBase] using below)
  refine ⟨finish, execution, post,
    arena.cons_of_rooted rooted headFits capacity cursor initialized frame, ?_⟩
  simpa only [Heap.cons_object, Function.update_self] using post.base_reg

/-- One measured execution allocates the real three-word node, returns its
placed address and establishes the ordinary `head :: values` observation.
The runtime postcondition also gives the exact cursor, contents and memory,
register and I/O frames. Existing lists may share the supplied tail. -/
theorem cons_measured {program : Ram.Program} {control depth : Nat}
    (registers : Source.Arena.Node.Registers)
    (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {head : CellValue τ} {tail : Option (NodeRef τ)}
    {values : List (CellValue τ)}
    (observed : NodeRef.Contents heap tail values)
    (headFits : cellToNat head < 2 ^ w)
    (capacity : next + 3 ≤ heapLimit)
    (headReg : entry.regs registers.head = cellWord w head)
    (tagReg : entry.regs registers.tag = (if tail.isSome then 1 else 0))
    (tailReg : entry.regs registers.tail = tail.elim 0 (fun ref => placement ref.object)) :
    ∃ finish, Source.LocalMeasuredExec control program heapLimit depth registers.allocate
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) registers.allocate)
        entry finish ∧
      registers.Post heapLimit (BitVec.ofNat w next) (cellWord w head)
        (if tail.isSome then 1 else 0) (tail.elim 0 (fun ref => placement ref.object))
        entry finish ∧
      ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
        (next + 3) heapLimit (heap.cons head tail).2 finish ∧
      finish.regs registers.base =
        (Function.update placement heap.objects.size (BitVec.ofNat w next))
          (heap.cons head tail).1.object ∧
      NodeRef.Contents (heap.cons head tail).2
        (some (heap.cons head tail).1) (head :: values) := by
  have rooted : ValueRooted heap (τ := .option (.node τ)) tail := by
    cases tail with
    | none => trivial
    | some ref => exact observed.root_lt_size
  obtain ⟨finish, execution, post, represented, returned⟩ :=
    cons_measured_of_rooted (program := program) (control := control) (depth := depth)
      registers arena rooted headFits capacity headReg tagReg tailReg
  exact ⟨finish, execution, post, represented, returned, Heap.cons_contents head observed⟩

end Ram.LanguageCompiler.ArenaRep
