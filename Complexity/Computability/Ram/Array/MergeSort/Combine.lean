/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Basic
import Complexity.Computability.Ram.Array.TwoBuffer
import Complexity.Tactic.Ram.Basic

/-!
# The actual merge-and-copy-back block for merge sort

Registers 5–8 retain source base, scratch base, total length, and split point.
The ordinary assignments below set up the already verified merge program,
then set up the already verified copy program to put the result back into the
source buffer. Both buffers contain standard `List.merge` on completion.

This is a nonrecursive composition block, not an assumed merge-sort step:
all setup assignments, both loops, and every copied word are charged by the
existing execution contracts. Its two-buffer frame is sufficient to combine
independent recursive calls on subarrays in a later module.
-/

namespace Ram.Source.Array.MergeSort.Combine

def mergeSetup : Stmt :=
  .seq (.assign 0 (.var 5))
    (.seq (.assign 1 (.bin .add (.var 5) (.var 8)))
      (.seq (.assign 2 (.var 6))
        (.seq (.assign 3 (.var 8))
          (.assign 4 (.bin .sub (.var 7) (.var 8))))))

def copySetup : Stmt :=
  .seq (.assign 0 (.var 6)) (.seq (.assign 1 (.var 5)) (.assign 2 (.var 7)))

def program : Stmt := .seq mergeSetup (.seq Merge.program (.seq copySetup copy))

def mergeState (s : State w) : State w :=
  ((((s.setReg 0 (s.regs 5)).setReg 1 (s.regs 5 + s.regs 8)).setReg 2
    (s.regs 6)).setReg 3 (s.regs 8)).setReg 4 (s.regs 7 - s.regs 8)

def copyState (s : State w) : State w :=
  ((s.setReg 0 (s.regs 6)).setReg 1 (s.regs 5)).setReg 2 (s.regs 7)

theorem mergeSetup_total_contract {heapLimit depth : Nat} {functions : Program}
    (s : State w) : TotalContract functions heapLimit depth mergeSetup
      (fun t => t = s) (fun t => t = mergeState s) := by
  ram_total_vc t ht [mergeSetup, mergeState, ht]

theorem copySetup_total_contract {heapLimit depth : Nat} {functions : Program}
    (s : State w) : TotalContract functions heapLimit depth copySetup
      (fun t => t = s) (fun t => t = copyState s) := by
  ram_total_vc t ht [copySetup, copyState, ht]

theorem mergeSetup_contract {control heapLimit depth : Nat} {functions : Program}
    (s : State w) : Contract control functions heapLimit depth mergeSetup
      (fun t => t = s) (fun t => t = mergeState s) (fun _ => 14) := by
  ram_vc t ht [mergeSetup, mergeState, ht]

theorem copySetup_contract {control heapLimit depth : Nat} {functions : Program}
    (s : State w) : Contract control functions heapLimit depth copySetup
      (fun t => t = s) (fun t => t = copyState s) (fun _ => 6) := by
  ram_vc t ht [copySetup, copyState, ht]

theorem mergeState_other (s : State w) {r : Reg} (hr : 5 ≤ r) :
    (mergeState s).regs r = s.regs r := by
  have h0 : r ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 5) hr)
  have h1 : r ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1 < 5) hr)
  have h2 : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 5) hr)
  have h3 : r ≠ 3 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 3 < 5) hr)
  have h4 : r ≠ 4 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 4 < 5) hr)
  simp [mergeState, State.setReg, h0, h1, h2, h3, h4]

theorem copyState_other (s : State w) {r : Reg} (hr : 3 ≤ r) :
    (copyState s).regs r = s.regs r := by
  have h0 : r ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 3) hr)
  have h1 : r ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1 < 3) hr)
  have h2 : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 3) hr)
  simp [copyState, State.setReg, h0, h1, h2]

structure Pre (heapLimit : Nat) (source scratch : Word w)
    (left right workspace : List (Word w)) (s : State w) : Prop where
  source_array : ArrayAt heapLimit source (left ++ right) s
  scratch_array : ArrayAt heapLimit scratch workspace s
  scratch_length : workspace.length = left.length + right.length
  disjoint : ArraysDisjoint source (left.length + right.length)
    scratch (left.length + right.length)
  source_reg : s.regs 5 = source
  scratch_reg : s.regs 6 = scratch
  length_reg : (s.regs 7).toNat = left.length + right.length
  split_reg : (s.regs 8).toNat = left.length

structure Post (heapLimit : Nat) (source scratch : Word w)
    (left right : List (Word w)) (entry finish : State w) : Prop where
  source_array : ArrayAt heapLimit source (unsignedMerge left right) finish
  scratch_array : ArrayAt heapLimit scratch (unsignedMerge left right) finish
  frame : TwoBufferFrame source (left.length + right.length)
    scratch (left.length + right.length) entry.mem finish.mem
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → finish.regs r = entry.regs r

theorem wellFormed {locals : Nat} (h : 9 ≤ locals) : program.WellFormed locals := by
  have h0 : 0 < locals := by omega
  have h1 : 1 < locals := by omega
  have h2 : 2 < locals := by omega
  have h3 : 3 < locals := by omega
  have h4 : 4 < locals := by omega
  have h5 : 5 < locals := by omega
  have h6 : 6 < locals := by omega
  have h7 : 7 < locals := by omega
  have h8 : 8 < locals := by omega
  simp [program, mergeSetup, copySetup, Stmt.WellFormed, Expr.Bounded,
    Merge.wellFormed (Nat.le_trans (by decide : 5 ≤ 9) h),
    copy_wellFormed (Nat.le_trans (by decide : 3 ≤ 9) h),
    h0, h1, h2, h3, h4, h5, h6, h7, h8]

theorem callsValid (functions : Program) : Compiler.CallsValid functions program := by
  simp [program, mergeSetup, copySetup, Compiler.CallsValid,
    Merge.callsValid functions, copy, copyBody]

theorem code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable program = 121 := rfl

private theorem merge_pre {heapLimit : Nat} {source scratch : Word w}
    {left right workspace : List (Word w)} {entry : State w}
    (hp : Pre heapLimit source scratch left right workspace entry) :
    Merge.Pre heapLimit source (arrayAddr source left.length) scratch
      left right workspace (mergeState entry) := by
  have hleft : ArrayAt heapLimit source left (mergeState entry) := by
    have h := hp.source_array.take left.length
    have h' : ArrayAt heapLimit source left entry := by simpa using h
    exact h'.of_mem_eq rfl
  have hright : ArrayAt heapLimit (arrayAddr source left.length) right (mergeState entry) := by
    have h := hp.source_array.drop (offset := left.length) (by simp)
    have h' : ArrayAt heapLimit (arrayAddr source left.length) right entry := by simpa using h
    exact h'.of_mem_eq rfl
  have hsplit : entry.regs 8 = BitVec.ofNat w left.length := by
    rw [← hp.split_reg, Word.ofNat_toNat_self]
  have hremaining : (entry.regs 7 - entry.regs 8).toNat = right.length := by
    change (BinOp.eval .sub (entry.regs 7) (entry.regs 8)).toNat = right.length
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hp.length_reg, hp.split_reg]; omega),
      hp.length_reg, hp.split_reg]
    omega
  refine ⟨hleft, hright, hp.scratch_array.of_mem_eq rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mergeState, State.setReg, hp.source_reg]
  · simp [mergeState, State.setReg, hp.source_reg, hsplit, arrayAddr]
  · simp [mergeState, State.setReg, hp.scratch_reg]
  · simpa [mergeState, State.setReg] using hp.split_reg
  · simpa [mergeState, State.setReg] using hremaining

private theorem merge_disjoint {heapLimit : Nat} {source scratch : Word w}
    {left right workspace : List (Word w)} {entry : State w}
    (hp : Pre heapLimit source scratch left right workspace entry) :
    ArraysDisjoint scratch (left.length + right.length) source left.length ∧
      ArraysDisjoint scratch (left.length + right.length)
        (arrayAddr source left.length) right.length := by
  have hwhole : ArraysDisjoint scratch (left.length + right.length) source (left ++ right).length := by
    simpa only [List.length_append] using hp.disjoint.symm
  constructor
  · have h := ArraysDisjoint.slice_right hp.source_array.1
      (offset := 0) (length := left.length) (by simp) hwhole
    simpa [arrayAddr] using h
  · exact ArraysDisjoint.slice_right hp.source_array.1 (by simp) hwhole

private theorem copy_pre {heapLimit : Nat} {source scratch : Word w}
    {left right workspace : List (Word w)} {entry merged : State w}
    (hp : Pre heapLimit source scratch left right workspace entry)
    (hm : Merge.Post heapLimit source (arrayAddr source left.length) scratch
      left right (mergeState entry) merged) :
    CopyPre heapLimit scratch source (unsignedMerge left right) (left ++ right)
      (copyState merged) := by
  have hmerged (r : Reg) (hr : 5 ≤ r) : merged.regs r = entry.regs r :=
    (hm.other r hr).trans (mergeState_other entry hr)
  have hsource : ArrayAt heapLimit source (left ++ right) merged :=
    hp.source_array.frame hm.frame (by simpa only [List.length_append] using hp.disjoint.symm)
  refine ⟨hm.destination_array.of_mem_eq rfl, hsource.of_mem_eq rfl, ?_, ?_, ?_⟩
  · simp [copyState, State.setReg, hmerged 6 (by decide), hp.scratch_reg]
  · simp [copyState, State.setReg, hmerged 5 (by decide), hp.source_reg]
  · simpa [copyState, State.setReg, hmerged 7 (by decide), length_unsignedMerge] using hp.length_reg

private theorem post {heapLimit : Nat} {source scratch : Word w}
    {left right : List (Word w)} {entry merged finish : State w}
    (hm : Merge.Post heapLimit source (arrayAddr source left.length) scratch
      left right (mergeState entry) merged)
    (hf : CopyPost heapLimit scratch source (unsignedMerge left right)
      (copyState merged) finish) :
    Post heapLimit source scratch left right entry finish := by
  have hmergeFrame : TwoBufferFrame source (left.length + right.length)
      scratch (left.length + right.length) entry.mem merged.mem :=
    TwoBufferFrame.of_right hm.frame
  have hcopyFrame : TwoBufferFrame source (left.length + right.length)
      scratch (left.length + right.length) merged.mem finish.mem := by
    apply TwoBufferFrame.of_left
    simpa only [length_unsignedMerge] using hf.frame
  refine ⟨hf.destination_array, hf.source_array, hmergeFrame.trans hcopyFrame,
    hf.input.trans hm.input, hf.output.trans hm.output, ?_⟩
  intro r hr
  have h3 : 3 ≤ r := Nat.le_trans (by decide : 3 ≤ 5) hr
  exact (hf.other r h3).trans ((copyState_other merged h3).trans
    ((hm.other r hr).trans (mergeState_other entry hr)))

theorem total_contract {heapLimit depth : Nat} {functions : Program}
    {source scratch : Word w} {left right workspace : List (Word w)} (hw : 0 < w) :
    TotalRelContract functions heapLimit depth program
      (Pre heapLimit source scratch left right workspace)
      (Post heapLimit source scratch left right) := by
  intro entry hp
  obtain ⟨_, hsetup, rfl⟩ := mergeSetup_total_contract (functions := functions)
    (heapLimit := heapLimit) (depth := depth) entry entry rfl
  obtain ⟨hdl, hdr⟩ := merge_disjoint hp
  obtain ⟨merged, hmerge, hm⟩ :=
    Merge.total_contract (functions := functions) (depth := depth)
      hw hp.scratch_length hdl hdr (mergeState entry) (merge_pre hp)
  obtain ⟨_, hcopySetup, rfl⟩ := copySetup_total_contract (functions := functions)
    (heapLimit := heapLimit) (depth := depth) merged merged rfl
  have hcopyLength : (left ++ right).length = (unsignedMerge left right).length := by
    simp only [List.length_append, length_unsignedMerge]
  have hcopyDisjoint : ArraysDisjoint scratch (unsignedMerge left right).length
      source (unsignedMerge left right).length := by
    simpa only [length_unsignedMerge] using hp.disjoint.symm
  obtain ⟨finish, hcopy, hf⟩ :=
    copy_total_contract (program := functions) (depth := depth)
      hw hcopyLength hcopyDisjoint (copyState merged) (copy_pre hp hm)
  exact ⟨finish, .seq hsetup (.seq hmerge (.seq hcopySetup hcopy)), post hm hf⟩

theorem timeBound {control heapLimit depth : Nat} {functions : Program}
    {source scratch : Word w} {left right workspace : List (Word w)} (hw : 0 < w) :
    TimeBound control functions heapLimit depth program
      (Pre heapLimit source scratch left right workspace)
      (fun _ => 53 * (left.length + right.length) + 26) := by
  intro entry hp steps finish hx
  change LocalMeasuredExec control functions heapLimit depth
    (.seq mergeSetup (.seq Merge.program (.seq copySetup copy))) steps entry finish at hx
  cases hx with
  | seq hsetup hrest =>
    have hsetupBound := (mergeSetup_contract (control := control) (functions := functions)
      (heapLimit := heapLimit) (depth := depth) entry).timeBound entry rfl _ _ hsetup
    obtain ⟨_, hprepared, rfl⟩ := mergeSetup_total_contract (functions := functions)
      (heapLimit := heapLimit) (depth := depth) entry entry rfl
    have hpreparedEq := hsetup.erase.deterministic hprepared
    rw [hpreparedEq] at hrest
    cases hrest with
    | seq hmerge hcopyRest =>
      obtain ⟨hdl, hdr⟩ := merge_disjoint hp
      have hmergeBound := Merge.timeBound (control := control) (functions := functions)
        (depth := depth) hw hp.scratch_length hdl hdr
          (mergeState entry) (merge_pre hp) _ _ hmerge
      obtain ⟨merged, hmerged, hm⟩ :=
        Merge.total_contract (functions := functions) (depth := depth)
          hw hp.scratch_length hdl hdr (mergeState entry) (merge_pre hp)
      have hmergedEq := hmerge.erase.deterministic hmerged
      rw [hmergedEq] at hcopyRest
      cases hcopyRest with
      | seq hcopySetup hcopy =>
        have hcopySetupBound := (copySetup_contract (control := control) (functions := functions)
          (heapLimit := heapLimit) (depth := depth) merged).timeBound merged rfl _ _ hcopySetup
        obtain ⟨_, hready, rfl⟩ := copySetup_total_contract (functions := functions)
          (heapLimit := heapLimit) (depth := depth) merged merged rfl
        have hreadyEq := hcopySetup.erase.deterministic hready
        rw [hreadyEq] at hcopy
        have hcopyLength : (left ++ right).length = (unsignedMerge left right).length := by
          simp only [List.length_append, length_unsignedMerge]
        have hcopyDisjoint : ArraysDisjoint scratch (unsignedMerge left right).length
            source (unsignedMerge left right).length := by
          simpa only [length_unsignedMerge] using hp.disjoint.symm
        have hcopyBound := copy_timeBound (control := control) (program := functions)
          (depth := depth) hw hcopyLength hcopyDisjoint
            (copyState merged) (copy_pre hp hm) _ _ hcopy
        change _ ≤ 14 at hsetupBound
        change _ ≤ 6 at hcopySetupBound
        change _ ≤ 34 * (left.length + right.length) + 4 at hmergeBound
        change _ ≤ 19 * (unsignedMerge left right).length + 2 at hcopyBound
        rw [length_unsignedMerge] at hcopyBound
        dsimp only
        omega

/-- Merge the two adjacent source halves into scratch, then copy the actual
merged words back to source. The input halves need not be sorted; their
contents are interpreted by standard `List.merge` either way. -/
theorem contract {control heapLimit depth : Nat} {functions : Program}
    {source scratch : Word w} {left right workspace : List (Word w)} (hw : 0 < w) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit source scratch left right workspace)
      (Post heapLimit source scratch left right)
      (fun _ => 53 * (left.length + right.length) + 26) :=
  (total_contract hw).with_timeBound (timeBound hw)

end Ram.Source.Array.MergeSort.Combine
