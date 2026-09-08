/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Measured.Memory
import Complexity.Computability.Ram.Compiler.Local.Program.Basic
import Complexity.Computability.Ram.Execution.Memory

/-!
# Heap footprints of complete checked local-frame programs

The actual header read and final halt add no heap accesses or writes. Thus a
bound proved for the main execution segment applies unchanged to the complete
executable, while its time still includes both transitions. These equalities
do not themselves bound the main segment or identify footprint with live space.
The recursive simulation below supplies the sufficient address bound for that
main segment and transports it to the complete executable and every write.
-/

namespace Ram.LocalCompiler

/-- Removing the real prologue and final halt preserves both heap footprints.
The main segment still includes all recursive calls and their ABI operations. -/
theorem rawLink_heapFootprints_eq_main {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    heapAccesses (rawLink control program main) (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) =
      heapAccesses (rawLink control program main) steps
        (mainStart control heapLimit input) ∧
    heapWrites (rawLink control program main) (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) =
      heapWrites (rawLink control program main) steps
        (mainStart control heapLimit input) := by
  obtain ⟨finish, hbody, hmatch, _, _, hpc⟩ :=
    main_run_measured hvalid hcodefit hstackfit hx
  have hfetch : (rawLink control program main)[finish.pc]? = some .halt := by
    rw [hpc, mainStart_pc]
    exact rawLink_halt control program main
  have hprologue := prologue_exec control program main heapLimit input
  have hcount : steps + 2 = 1 + steps + 1 := by omega
  constructor
  · rw [hcount, heapAccesses_add (hprologue.trans hbody),
      heapAccesses_add hprologue, heapAccesses_one, heapAccesses_one,
      stepHeapAccesses_of_fetch rfl (rawLink_prologue control program main),
      stepHeapAccesses_of_fetch hmatch.running hfetch]
    simp [Instr.heapAccesses]
  · rw [hcount, heapWrites_add (hprologue.trans hbody),
      heapWrites_add hprologue, heapWrites_one, heapWrites_one,
      stepHeapWrites_of_fetch rfl (rawLink_prologue control program main),
      stepHeapWrites_of_fetch hmatch.running hfetch]
    simp [Instr.heapWrites]

/-- Successful checked compilation supplies the static premises for the same
complete-executable footprint equalities. -/
theorem compileChecked_heapFootprints_eq_main {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) :
    heapAccesses code (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) =
      heapAccesses code steps (mainStart control heapLimit input) ∧
    heapWrites code (steps + 2)
        (State.initial (BitVec.ofNat w heapLimit :: input)) =
      heapWrites code steps (mainStart control heapLimit input) := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_heapFootprints_eq_main hvalid hcodefit hstackfit hx

/-- The main segment starts with SP equal to the declared heap boundary. Its
recursive address envelope therefore has no unknown preloaded-stack offset. -/
theorem main_heapAccesses_below {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) {address : Word w}
    (member : address ∈ heapAccesses (rawLink control program main) steps
      (mainStart control heapLimit input)) :
    address.toNat < heapLimit + depth * ABI.frameSize control := by
  have hh : heapLimit < 2 ^ w := by omega
  have hsp : ((mainStart control heapLimit input).regs (ABI.sp control)).toNat =
      heapLimit := by
    rw [mainStart_sp, Word.ofNat_toNat_of_lt hh]
  have hfit : Compiler.StackFits control depth (mainStart control heapLimit input) := by
    change ((mainStart control heapLimit input).regs (ABI.sp control)).toNat +
      depth * ABI.frameSize control < 2 ^ w
    rw [hsp]
    exact hstackfit
  have access := (simulate_measured_memory hvalid hcodefit hx hvalid.1).2
    (Nat.le_refl control) (mainStart control heapLimit input)
    (mainStart_matches control heapLimit input)
    (by rw [hsp]) hfit
    (by simpa only [mainStart_pc] using rawLink_main control program main)
    address member
  simpa only [hsp] using access

/-- Every actual heap access of the complete recursive executable is below
its sufficient source-heap-plus-stack address capacity. -/
theorem rawLink_heapAccesses_below {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {input : List (Word w)}
    {sourceFinal : Source.State w} (hvalid : Valid control program main)
    (hcodefit : (rawLink control program main).length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) {address : Word w}
    (member : address ∈ heapAccesses (rawLink control program main) (steps + 2)
      (State.initial (BitVec.ofNat w heapLimit :: input))) :
    address.toNat < heapLimit + depth * ABI.frameSize control := by
  rw [(rawLink_heapFootprints_eq_main hvalid hcodefit hstackfit hx).1] at member
  exact main_heapAccesses_below hvalid hcodefit hstackfit hx member

/-- Successful checked compilation supplies validity for the complete target
access bound; the program and exact execution count are unchanged. -/
theorem compileChecked_heapAccesses_below {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) {address : Word w}
    (member : address ∈ heapAccesses code (steps + 2)
      (State.initial (BitVec.ofNat w heapLimit :: input))) :
    address.toNat < heapLimit + depth * ABI.frameSize control := by
  obtain ⟨hvalid, rfl⟩ := compileChecked_some_iff.mp hcompile
  exact rawLink_heapAccesses_below hvalid hcodefit hstackfit hx member

/-- The same bound includes every compiler-generated write, not only source
stores or writes that change the previous contents. -/
theorem compileChecked_heapWrites_below {control heapLimit depth steps : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal) {address : Word w}
    (member : address ∈ heapWrites code (steps + 2)
      (State.initial (BitVec.ofNat w heapLimit :: input))) :
    address.toNat < heapLimit + depth * ABI.frameSize control :=
  compileChecked_heapAccesses_below hcompile hcodefit hstackfit hx
    (heapWrites_subset_accesses _ _ _ member)

/-- Every real prefix preserves cells outside the sufficient address capacity.
This excludes temporary writes there, not merely differing final contents. -/
theorem compileChecked_prefix_mem_above {control heapLimit depth steps k : Nat}
    {program : Program} {main : Stmt} {code : Code} {input : List (Word w)}
    {sourceFinal : Source.State w} {current : State w}
    (hcompile : compileChecked control program main = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hx : Source.LocalMeasuredExec control program heapLimit depth main steps
      (Source.State.initial input) sourceFinal)
    (hk : k ≤ steps + 2)
    (execution : Exec code k (State.initial (BitVec.ofNat w heapLimit :: input)) current)
    {address : Word w} (above : heapLimit + depth * ABI.frameSize control ≤ address.toNat) :
    current.mem address = (State.initial (BitVec.ofNat w heapLimit :: input)).mem address := by
  apply execution.prefix_mem_eq_of_not_written hk
  intro member
  exact Nat.not_lt_of_ge above
    (compileChecked_heapWrites_below hcompile hcodefit hstackfit hx member)

end Ram.LocalCompiler
