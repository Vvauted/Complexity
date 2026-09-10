/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Allocation
import Complexity.Computability.Ram.Memory.Arena.Function

/-!
# Actual allocation of a typed source object

The real allocator's initialization loop supplies the contents and frame needed
by `ArenaRep.alloc`. The returned descriptor, extended source heap and final RAM
memory therefore come from one execution. The mathematical initial scalar must
fit its target word; capacity supplies the length and address ranges.

This module supplies the callable allocation primitive connection. General
simulation of typed `Stmt.alloc` bodies is in `Arena.MeasuredSimulation`, with
the compiled function runner in `Arena.ProgramExecution`. Function setup and
return use the existing verified backend.
-/

namespace Ram.LanguageCompiler.ArenaRep

open Complexity.Language

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Complexity.Language.Heap} {entry : Source.State w}

/-- The actual callable allocator creates precisely the source object and its
descriptor, retaining the advanced cursor through caller-register restoration. -/
theorem function_measured {program : Ram.Program} {control depth length : Nat}
    (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {initial : CellValue τ}
    (initialFits : cellToNat initial < 2 ^ w) (capacity : next + length ≤ heapLimit) :
    ∃ finish, Source.FunctionMeasuredExec control program heapLimit depth Source.Arena.function
        [BitVec.ofNat w length, cellWord w initial] (14 * length + 14) entry
        (valueWords (Function.update placement heap.objects.size (BitVec.ofNat w next))
          (τ := .buffer τ) (heap.alloc length initial).1) finish ∧
      ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
        (next + length) heapLimit (heap.alloc length initial).2 finish := by
  have nextFits := lt_of_le_of_lt arena.cursor_le arena.limit_lt
  have exactBase : (BitVec.ofNat w next).toNat = next := Word.ofNat_toNat_of_lt nextFits
  obtain ⟨finish, executed, cursor, initialized, frame, _, _⟩ :=
    Source.Arena.function_measured (program := program) (control := control) (depth := depth)
      entry arena.cursor_eq (by simpa only [exactBase] using arena.cursor_pos)
      (by simpa only [exactBase] using capacity) arena.limit_lt
  refine ⟨finish, ?_, arena.alloc initialFits capacity ?_ ?_ ?_⟩
  · simpa [valueWords_buffer, Complexity.Language.Heap.alloc, arrayAddr] using executed
  · simpa only [arrayAddr, BitVec.ofNat_add_ofNat] using cursor
  · simpa only [objectWords, Array.map_replicate, Array.toList_replicate] using initialized
  · intro address positive below
    apply frame address
    · intro zero
      simp [zero] at positive
    · exact Or.inl (by simpa only [exactBase] using below)

/-- A later allocation preserves an already returned view at its original RAM
address. Aliases among old objects are allowed, and the new array may be empty. -/
theorem function_measured_preserving {program : Ram.Program} {control depth length : Nat}
    (arena : ArenaRep placement next heapLimit heap entry)
    {τ σ : CellTy} {initial : CellValue τ} {buffer : Buffer σ}
    {contents : Array (CellValue σ)} (observed : buffer.Contents heap contents)
    (lengthFits : buffer.length < 2 ^ w)
    (initialFits : cellToNat initial < 2 ^ w) (capacity : next + length ≤ heapLimit) :
    ∃ finish, Source.FunctionMeasuredExec control program heapLimit depth Source.Arena.function
        [BitVec.ofNat w length, cellWord w initial] (14 * length + 14) entry
        (valueWords (Function.update placement heap.objects.size (BitVec.ofNat w next))
          (τ := .buffer τ) (heap.alloc length initial).1) finish ∧
      ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
        (next + length) heapLimit (heap.alloc length initial).2 finish ∧
      (bufferRef placement buffer).Rep heapLimit (objectWords w contents).toList finish := by
  obtain ⟨finish, invocation, represented⟩ :=
    arena.function_measured (program := program) (control := control) (depth := depth)
      initialFits capacity
  refine ⟨finish, invocation, represented, ?_⟩
  have agreed := Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
    (BitVec.ofNat w next)
  rw [agreed.bufferRef observed.valid.rooted]
  exact represented.heapRep.view (observed.alloc length initial) lengthFits

/-- A checked compiled invocation returns the source allocation's encoded result
and represents its actual final heap. The exact count includes call and halt;
bootstrap and preloaded input preparation remain separate boundaries. -/
theorem function_runUntil {program : Ram.Program} {control fn length : Nat} {code : Code}
    (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {initial : CellValue τ}
    (initialFits : cellToNat initial < 2 ^ w) (capacity : next + length ≤ heapLimit)
    (compiled : LocalCompiler.Function.compile control program fn 2 = some code)
    (lookup : program[fn]? = some Source.Arena.function)
    (codeFits : code.length < 2 ^ w)
    (stackFits : heapLimit + ABI.frameSize control < 2 ^ w) :
    ∃ finish target,
      LocalCompiler.Function.runUntil control program fn 2 heapLimit
          [BitVec.ofNat w length, cellWord w initial] entry =
        some ⟨target, 14 * length + 69, .halted⟩ ∧
      LocalCompiler.Function.returnedValues 2 target =
        valueWords (Function.update placement heap.objects.size (BitVec.ofNat w next))
          (τ := .buffer τ) (heap.alloc length initial).1 ∧
      Source.State.Observes heapLimit 0 finish target ∧
      ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
        (next + length) heapLimit (heap.alloc length initial).2 finish := by
  obtain ⟨finish, invocation, represented⟩ :=
    arena.function_measured (program := program) (control := control) (depth := 0)
      initialFits capacity
  obtain ⟨target, returned, fields, observed⟩ :=
    LocalCompiler.Function.runUntil_eq_of_measured compiled lookup codeFits
      (by simpa using stackFits) invocation
  exact ⟨finish, target, by simpa only [Source.Arena.function_callSteps] using returned,
    fields, observed, represented⟩

end Ram.LanguageCompiler.ArenaRep
