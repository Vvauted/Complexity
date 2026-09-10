/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Arena.Registers.Allocation

/-!
# Standalone arena allocation

The standalone function specializes the shared allocator proof to its existing
five-register ABI. Its statements, execution and exact counts are unchanged.
Inline allocation uses the same parameterized proof at fresh local slots.
-/

namespace Ram.Source.Arena

/-- State after the actual reservation and cursor setup. -/
def prepared (s : State w) : State w := Registers.legacy.prepared s

/-- State after one actual initialization store and two local assignments. -/
def fillStep (s : State w) : State w := Registers.legacy.fillStep s

theorem prepare_safe {program : Program} {heapLimit depth : Nat}
    (s : State w) (positive : 0 < heapLimit) :
    SafeExec program heapLimit depth prepare s (prepared s) :=
  Registers.legacy.prepare_safe s positive

theorem prepare_localMeasured {program : Program} {control heapLimit depth : Nat}
    (s : State w) (positive : 0 < heapLimit) :
    LocalMeasuredExec control program heapLimit depth prepare 12 s (prepared s) :=
  Registers.legacy.prepare_localMeasured s positive

theorem fillBody_safe {program : Program} {heapLimit depth : Nat}
    (s : State w) (address : (s.regs 3).toNat < heapLimit) :
    SafeExec program heapLimit depth fillBody s (fillStep s) :=
  Registers.legacy.fillBody_safe s address

theorem fillBody_result {program : Program} {heapLimit depth : Nat} {s t : State w}
    (execution : SafeExec program heapLimit depth fillBody s t) : t = fillStep s :=
  Registers.legacy.fillBody_result execution

theorem fillBody_localMeasured {program : Program} {control heapLimit depth : Nat}
    {s t : State w} (safe : SafeExec program heapLimit depth fillBody s t) :
    LocalMeasuredExec control program heapLimit depth fillBody 11 s t :=
  Registers.legacy.fillBody_localMeasured safe

/-- Every completed filling loop has this exact count, including an empty loop. -/
theorem fill_localMeasured {program : Program} {control heapLimit depth : Nat}
    (hw : 0 < w) {s t : State w}
    (safe : SafeExec program heapLimit depth fill s t) :
    LocalMeasuredExec control program heapLimit depth fill
      (14 * (s.regs 4).toNat + 2) s t :=
  Registers.legacy.fill_localMeasured hw safe

/-- Filling begins with no initialized cells and preserves the surrounding heap. -/
theorem fill_safe {program : Program} {heapLimit depth length : Nat}
    {base value : Word w} (hw : 0 < w) (entry : State w)
    (pointer : entry.regs 3 = base) (count : (entry.regs 4).toNat = length)
    (initial : entry.regs 1 = value)
    (capacity : base.toNat + length ≤ heapLimit) (fits : heapLimit < 2 ^ w) :
    ∃ finish, SafeExec program heapLimit depth fill entry finish ∧
      InitializedPrefix entry.mem finish.mem base value length ∧
      finish.regs 4 = 0 ∧ finish.input = entry.input ∧ finish.outputRev = entry.outputRev :=
  Registers.legacy.fill_safe hw entry pointer count initial capacity fits

/-- The standalone allocator retains its exact body count, including length zero. -/
theorem allocate_measured {program : Program} {control heapLimit depth length : Nat}
    {base value : Word w} {entry : State w} (pre : Pre heapLimit base length value entry) :
    ∃ finish, LocalMeasuredExec control program heapLimit depth allocate
      (14 * length + 14) entry finish ∧ Post heapLimit base length value entry finish := by
  have configured : Registers.legacy.Pre heapLimit base length value entry :=
    ⟨pre.cursor, pre.length_reg, pre.value_reg, pre.positive, pre.capacity, pre.fits⟩
  obtain ⟨finish, execution, post⟩ :=
    Registers.legacy.allocate_measured (program := program) (control := control)
      (depth := depth) configured
  refine ⟨finish, execution, ⟨post.cursor, post.array, post.base_reg, post.length_reg,
    post.frame, post.input, post.output, ?_⟩⟩
  intro slot bound
  exact post.other slot
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 5) bound))
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 3 < 5) bound))
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 4 < 5) bound))

/-- Functional correctness does not require choosing a time budget. -/
theorem allocate_total {program : Program} {heapLimit depth length : Nat}
    {base value : Word w} :
    TotalRelContract program heapLimit depth allocate
      (Pre heapLimit base length value) (Post heapLimit base length value) := by
  intro entry pre
  obtain ⟨finish, execution, post⟩ :=
    allocate_measured (program := program) (control := 0) (depth := depth) pre
  exact ⟨finish, execution.erase, post⟩

end Ram.Source.Arena
