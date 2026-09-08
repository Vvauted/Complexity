/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contents
import Complexity.Computability.Ram.Array.MergeSort.Combine
import Complexity.Computability.Ram.Array.MergeSort.Ordering
import Complexity.Computability.Ram.Array.TwoBuffer
import Complexity.Computability.Ram.Verification.Recursion.Basic
import Complexity.Computability.Ram.Verification.Recursion.Time
import Complexity.Computability.Recurrence.Balanced
import Complexity.Tactic.Ram.Total

/-!
# Recursive RAM merge sort with reusable contracts

One fixed three-argument function sorts an array using an equally sized,
disjoint scratch allocation. It recursively sorts the two subarrays, then
executes the proved merge-and-copy block. The recursion proof uses callable
`Recursion.Spec` hypotheses; all call, frame, comparison and copy costs come
from the existing compiler. Scratch contents are arbitrary at entry.
-/

namespace Ram.Source.Array.MergeSort

def condition : Expr := .bin .ult (.const 1) (.var 2)

def setup : Stmt :=
  .seq (.assign 5 (.var 0)) (.seq (.assign 6 (.var 1))
    (.seq (.assign 7 (.var 2)) (.assign 8 (.bin .udiv (.var 2) (.const 2)))))

def leftArgs : List Expr := [.var 5, .var 6, .var 8]
def rightArgs : List Expr :=
  [.bin .add (.var 5) (.var 8), .bin .add (.var 6) (.var 8),
    .bin .sub (.var 7) (.var 8)]

/-- The numeric index is resolved by the enclosing program's function table. -/
def function (selfFn : Nat) : Func where
  params := 3
  locals := 9
  body := .ite condition
    (.seq setup (.seq (.call 4 selfFn leftArgs)
      (.seq (.call 4 selfFn rightArgs) Combine.program))) .skip
  result := .const 0

def program : Program := [function 0]

structure Pre (heapLimit : Nat) (base scratch : Word w) (xs : List (Word w))
    (s : State w) : Prop where
  source_array : ArrayAt heapLimit base xs s
  scratch_array : ∃ workspace, workspace.length = xs.length ∧ ArrayAt heapLimit scratch workspace s
  disjoint : ArraysDisjoint base xs.length scratch xs.length
  base_reg : s.regs 0 = base
  scratch_reg : s.regs 1 = scratch
  length_reg : (s.regs 2).toNat = xs.length

structure Post (heapLimit : Nat) (base scratch : Word w) (xs : List (Word w))
    (entry finish : State w) : Prop where
  source_array : ArrayAt heapLimit base (sorted xs) finish
  scratch_array : ∃ workspace, workspace.length = xs.length ∧ ArrayAt heapLimit scratch workspace finish
  frame : TwoBufferFrame base xs.length scratch xs.length entry.mem finish.mem
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev

/-- Functional recursion specifies the represented result and safe stack
depth without choosing an instruction budget. -/
def totalSpec (heapLimit selfFn w : Nat) :
    Recursion.TotalSpec (function selfFn) w (List (Word w)) where
  pre xs s := Pre heapLimit (s.regs 0) (s.regs 1) xs s
  post xs entry finish := Post heapLimit (entry.regs 0) (entry.regs 1) xs entry finish
  depth xs := Nat.clog 2 xs.length

/-- The bound is a supersolution of the real two-child execution recurrence. -/
def budget (length : Nat) : Nat := Recurrence.balancedBudget 4 158 length

def recursionSpec (heapLimit selfFn w : Nat) : Recursion.Spec (function selfFn) w (List (Word w)) :=
  (totalSpec heapLimit selfFn w).withBudget (fun xs => budget xs.length)

theorem initialize_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable setup = 10 := rfl

/-- All nine frame saves/restores, three argument evaluations, and both
control transfers are included in these generated-list length identities. -/
theorem left_call_steps (control bodySteps : Nat) :
    (ABI.callPrefixLocals control 9 leftArgs 0).length + 1 + bodySteps +
      (ABI.returnCodeLocals control 9 (.const 0)).length + 1 = bodySteps + 81 := by
  change 46 + 1 + bodySteps + 33 + 1 = bodySteps + 81
  omega

theorem right_call_steps (control bodySteps : Nat) :
    (ABI.callPrefixLocals control 9 rightArgs 0).length + 1 + bodySteps +
      (ABI.returnCodeLocals control 9 (.const 0)).length + 1 = bodySteps + 87 := by
  change 52 + 1 + bodySteps + 33 + 1 = bodySteps + 87
  omega

theorem left_call_budget (heapLimit selfFn control w : Nat) (xs : List (Word w)) :
    (recursionSpec heapLimit selfFn w).callBudget control leftArgs xs = budget xs.length + 81 :=
  left_call_steps control (budget xs.length)

theorem right_call_budget (heapLimit selfFn control w : Nat) (xs : List (Word w)) :
    (recursionSpec heapLimit selfFn w).callBudget control rightArgs xs = budget xs.length + 87 :=
  right_call_steps control (budget xs.length)

def initialized (s : State w) : State w :=
  (((s.setReg 5 (s.regs 0)).setReg 6 (s.regs 1)).setReg 7 (s.regs 2)).setReg 8 (s.regs 2 / 2)

/-- Initialization changes only the four saved operands. No time bound is
needed to establish the entry state for the two recursive calls. -/
theorem initialize_total_contract {heapLimit depth : Nat} {functions : Program}
    (s : State w) : TotalContract functions heapLimit depth setup
      (fun t => t = s) (fun t => t = initialized s) := by
  ram_total_vc t ht [setup, initialized, ht]

theorem initialize_contract {control heapLimit depth : Nat} {functions : Program}
    (s : State w) : Contract control functions heapLimit depth setup
      (fun t => t = s) (fun t => t = initialized s) (fun _ => 10) := by
  ram_vc t ht [setup, initialized, ht]

private theorem half_toNat {heapLimit : Nat} {base scratch : Word w} {xs : List (Word w)}
    {s : State w} (hw : 2 ≤ w) (h : Pre heapLimit base scratch xs s) :
    (s.regs 2 / 2).toNat = xs.length / 2 := by
  have htwoFit : 2 < 2 ^ w := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have htwo : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt htwoFit
  rw [BitVec.toNat_udiv, h.length_reg, htwo]

theorem initialized_leftArgs {heapLimit : Nat} {base scratch : Word w}
    {xs : List (Word w)} {s : State w} (h : Pre heapLimit base scratch xs s) :
    leftArgs.map (initialized s).eval = [base, scratch, s.regs 2 / 2] := by
  simp [leftArgs, initialized, State.eval, Expr.eval, State.setReg, h.base_reg, h.scratch_reg]

structure Stage (heapLimit : Nat) (base scratch : Word w) (xs front back : List (Word w))
    (entry current : State w) : Prop where
  source_array : ArrayAt heapLimit base (front ++ back) current
  scratch_array : ∃ workspace, workspace.length = xs.length ∧ ArrayAt heapLimit scratch workspace current
  front_length : front.length = xs.length / 2
  back_length : back.length = xs.length - xs.length / 2
  source_reg : current.regs 5 = base
  scratch_reg : current.regs 6 = scratch
  length_reg : (current.regs 7).toNat = xs.length
  split_reg : (current.regs 8).toNat = xs.length / 2
  frame : TwoBufferFrame base xs.length scratch xs.length entry.mem current.mem
  input : current.input = entry.input
  output : current.outputRev = entry.outputRev

theorem left_pre {heapLimit selfFn : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry : State w} (hw : 2 ≤ w)
    (hp : Pre heapLimit base scratch xs entry) :
    (recursionSpec heapLimit selfFn w).pre (xs.take (xs.length / 2))
      ((initialized entry).enter (leftArgs.map (initialized entry).eval)) := by
  rw [initialized_leftArgs hp]
  change Pre heapLimit base scratch (xs.take (xs.length / 2)) _
  obtain ⟨workspace, hlen, hs⟩ := hp.scratch_array
  have hk : xs.length / 2 ≤ xs.length := Nat.div_le_self _ _
  have hkw : xs.length / 2 ≤ workspace.length := by omega
  refine ⟨(hp.source_array.take _).of_mem_eq rfl, ?_, ?_, rfl, rfl, ?_⟩
  · refine ⟨workspace.take (xs.length / 2), ?_, (hs.take _).of_mem_eq rfl⟩
    rw [List.length_take_of_le hk, List.length_take_of_le hkw]
  · have hd : ArraysDisjoint base xs.length scratch workspace.length := by
      simpa only [hlen] using hp.disjoint
    have h := ArraysDisjoint.slices hp.source_array.1 hs.1
      (firstOffset := 0) (firstLen := xs.length / 2)
      (secondOffset := 0) (secondLen := xs.length / 2) (by omega) (by omega) hd
    simpa [arrayAddr, List.length_take_of_le hk] using h
  · change (entry.regs 2 / 2).toNat = (xs.take (xs.length / 2)).length
    rw [half_toNat hw hp, List.length_take_of_le hk]

theorem after_left {heapLimit selfFn : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry callee : State w} (hw : 2 ≤ w)
    (hp : Pre heapLimit base scratch xs entry)
    (hc : (recursionSpec heapLimit selfFn w).post (xs.take (xs.length / 2))
      ((initialized entry).enter (leftArgs.map (initialized entry).eval)) callee) :
    Stage heapLimit base scratch xs (sorted (xs.take (xs.length / 2)))
      (xs.drop (xs.length / 2)) entry ((initialized entry).leave callee 4 (.const 0)) := by
  rw [initialized_leftArgs hp] at hc
  change Post heapLimit base scratch (xs.take (xs.length / 2)) _ callee at hc
  let k := xs.length / 2
  have hk : k ≤ xs.length := Nat.div_le_self _ _
  have htlen : (xs.take k).length = k := List.length_take_of_le hk
  obtain ⟨workspace, hlen, hs⟩ := hp.scratch_array
  let finish := (initialized entry).leave callee 4 (.const 0)
  have hf : TwoBufferFrame base k scratch k entry.mem finish.mem := by
    have hf' := hc.frame
    change TwoBufferFrame base (xs.take k).length scratch (xs.take k).length
      entry.mem finish.mem at hf'
    simpa only [htlen] using hf'
  have hdwhole : ArraysDisjoint base xs.length scratch workspace.length := by
    simpa only [hlen] using hp.disjoint
  have hdsecond : ArraysDisjoint scratch k (arrayAddr base k) (xs.drop k).length := by
    have h := ArraysDisjoint.slices hs.1 hp.source_array.1
      (firstOffset := 0) (firstLen := k) (secondOffset := k)
      (secondLen := (xs.drop k).length) (by omega) (by simp; omega) hdwhole.symm
    simpa [arrayAddr] using h
  have hright : ArrayAt heapLimit (arrayAddr base k) (xs.drop k) finish :=
    (hp.source_array.drop hk).frame_two hf
      (by simpa only [htlen] using hp.source_array.1.split_disjoint hk) hdsecond
  have hleft : ArrayAt heapLimit base (sorted (xs.take k)) finish := hc.source_array.leave _ _ _
  have hsum : (sorted (xs.take k)).length + (xs.drop k).length = xs.length := by
    rw [length_sorted, htlen, List.length_drop]
    omega
  have hfull : ArrayAt heapLimit base (sorted (xs.take k) ++ xs.drop k) finish :=
    hp.source_array.reassemble hleft (by simpa only [length_sorted, htlen] using hright) hsum
  have hframe : TwoBufferFrame base xs.length scratch xs.length entry.mem finish.mem := by
    have hf' : TwoBufferFrame (arrayAddr base 0) k (arrayAddr scratch 0) k entry.mem finish.mem := by
      simpa [arrayAddr] using hf
    have h := TwoBufferFrame.within hp.source_array.1 hs.1
      (by omega : 0 + k ≤ xs.length) (by omega : 0 + k ≤ workspace.length) hf'
    simpa only [hlen] using h
  refine ⟨hfull, ?_, ?_, List.length_drop, ?_, ?_, ?_, ?_, hframe, hc.input, hc.output⟩
  · obtain ⟨now, hn, ha⟩ := hs.exists_contents finish
    exact ⟨now, hn.trans hlen, ha⟩
  · rw [length_sorted, htlen]
  · simp [initialized, State.leave, State.setReg, hp.base_reg]
  · simp [initialized, State.leave, State.setReg, hp.scratch_reg]
  · simpa [finish, initialized, State.leave, State.setReg] using hp.length_reg
  · simpa [finish, initialized, State.leave, State.setReg] using half_toNat hw hp

theorem stage_rightArgs {heapLimit : Nat} {base scratch : Word w}
    {xs front back : List (Word w)} {entry caller : State w}
    (hs : Stage heapLimit base scratch xs front back entry caller) :
    rightArgs.map caller.eval =
      [arrayAddr base (xs.length / 2), arrayAddr scratch (xs.length / 2), caller.regs 7 - caller.regs 8] := by
  have hk : caller.regs 8 = BitVec.ofNat w (xs.length / 2) := by
    rw [← hs.split_reg, Word.ofNat_toNat_self]
  simp [rightArgs, State.eval, Expr.eval, BinOp.eval, hs.source_reg, hs.scratch_reg, hk, arrayAddr]

theorem right_pre {heapLimit selfFn : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry caller : State w}
    (hp : Pre heapLimit base scratch xs entry)
    (hs : Stage heapLimit base scratch xs (sorted (xs.take (xs.length / 2)))
      (xs.drop (xs.length / 2)) entry caller) :
    (recursionSpec heapLimit selfFn w).pre (xs.drop (xs.length / 2))
      (caller.enter (rightArgs.map caller.eval)) := by
  rw [stage_rightArgs hs]
  change Pre heapLimit (arrayAddr base (xs.length / 2))
    (arrayAddr scratch (xs.length / 2)) (xs.drop (xs.length / 2)) _
  let k := xs.length / 2
  have hk : k ≤ xs.length := Nat.div_le_self _ _
  have hwhole : ArrayAt heapLimit base (sorted (xs.take k) ++ xs.drop k) caller := hs.source_array
  have hsource : ArrayAt heapLimit (arrayAddr base k) (xs.drop k) caller := by
    have h := hwhole.drop (offset := (sorted (xs.take k)).length)
      (by rw [List.length_append]; exact Nat.le_add_right _ _)
    simp only [List.drop_left] at h
    rw [length_sorted, List.length_take_of_le hk] at h
    exact h
  obtain ⟨workspace, hlen, hspace⟩ := hs.scratch_array
  have hspace' := hspace.drop (offset := k) (by omega)
  refine ⟨hsource.enter _, ⟨workspace.drop k, ?_, hspace'.enter _⟩, ?_, rfl, rfl, ?_⟩
  · simp only [List.length_drop, hlen]
    rfl
  · obtain ⟨original, horiginal, ha⟩ := hp.scratch_array
    have hd : ArraysDisjoint base xs.length scratch original.length := by
      simpa only [horiginal] using hp.disjoint
    exact ArraysDisjoint.slices hp.source_array.1 ha.1
      (by simp; omega) (by simp; omega) hd
  · change (caller.regs 7 - caller.regs 8).toNat = (xs.drop k).length
    change (BinOp.eval .sub (caller.regs 7) (caller.regs 8)).toNat = _
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hs.length_reg, hs.split_reg]; exact hk),
      hs.length_reg, hs.split_reg, List.length_drop]

theorem after_right {heapLimit selfFn : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry caller callee : State w}
    (hp : Pre heapLimit base scratch xs entry)
    (hs : Stage heapLimit base scratch xs (sorted (xs.take (xs.length / 2)))
      (xs.drop (xs.length / 2)) entry caller)
    (hc : (recursionSpec heapLimit selfFn w).post (xs.drop (xs.length / 2))
      (caller.enter (rightArgs.map caller.eval)) callee) :
    Stage heapLimit base scratch xs (sorted (xs.take (xs.length / 2)))
      (sorted (xs.drop (xs.length / 2))) entry (caller.leave callee 4 (.const 0)) := by
  rw [stage_rightArgs hs] at hc
  change Post heapLimit (arrayAddr base (xs.length / 2)) (arrayAddr scratch (xs.length / 2))
    (xs.drop (xs.length / 2)) _ callee at hc
  let k := xs.length / 2
  have hk : k ≤ xs.length := Nat.div_le_self _ _
  have htlen : (xs.take k).length = k := List.length_take_of_le hk
  obtain ⟨workspace, hlen, hspace⟩ := hs.scratch_array
  have hwhole : ArrayAt heapLimit base (sorted (xs.take k) ++ xs.drop k) caller := hs.source_array
  let finish := caller.leave callee 4 (.const 0)
  have hf : TwoBufferFrame (arrayAddr base k) (xs.drop k).length
      (arrayAddr scratch k) (xs.drop k).length caller.mem finish.mem := hc.frame
  have hfront : ArrayAt heapLimit base (sorted (xs.take k)) caller := by
    have h := hwhole.take (sorted (xs.take k)).length
    simpa only [List.take_left] using h
  have hdsecond : ArraysDisjoint (arrayAddr scratch k) (xs.drop k).length
      base (sorted (xs.take k)).length := by
    have hd : ArraysDisjoint scratch workspace.length base xs.length := by
      simpa only [hlen] using hp.disjoint.symm
    have h := ArraysDisjoint.slices hspace.1 hp.source_array.1
      (firstOffset := k) (firstLen := (xs.drop k).length)
      (secondOffset := 0) (secondLen := k) (by simp; omega) (by omega) hd
    simpa [arrayAddr, length_sorted, htlen] using h
  have hleft : ArrayAt heapLimit base (sorted (xs.take k)) finish :=
    hfront.frame_two hf
      (by simpa only [length_sorted] using (hp.source_array.1.split_disjoint hk).symm)
      hdsecond
  have hright : ArrayAt heapLimit (arrayAddr base k) (sorted (xs.drop k)) finish :=
    hc.source_array.leave _ _ _
  have hsum : (sorted (xs.take k)).length + (sorted (xs.drop k)).length = xs.length := by
    simp only [length_sorted, htlen, List.length_drop]
    omega
  have hfull : ArrayAt heapLimit base (sorted (xs.take k) ++ sorted (xs.drop k)) finish :=
    hp.source_array.reassemble hleft (by simpa only [length_sorted, htlen] using hright) hsum
  have hframe : TwoBufferFrame base xs.length scratch xs.length caller.mem finish.mem := by
    have hsourceLen : (sorted (xs.take k) ++ xs.drop k).length = xs.length := by
      simp only [List.length_append, length_sorted, htlen, List.length_drop]
      omega
    have h := TwoBufferFrame.within hwhole.1 hspace.1
      (by rw [hsourceLen, List.length_drop]; omega)
      (by rw [hlen, List.length_drop]; omega) hf
    simpa only [hsourceLen, hlen] using h
  refine ⟨hfull, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.frame.trans hframe,
    hc.input.trans hs.input, hc.output.trans hs.output⟩
  · obtain ⟨now, hn, ha⟩ := hspace.exists_contents finish
    exact ⟨now, hn.trans hlen, ha⟩
  · rw [length_sorted, htlen]
  · rw [length_sorted, List.length_drop]
  · simpa [finish, State.leave] using hs.source_reg
  · simpa [finish, State.leave] using hs.scratch_reg
  · simpa [finish, State.leave] using hs.length_reg
  · simpa [finish, State.leave] using hs.split_reg

theorem combine_pre {heapLimit : Nat} {base scratch : Word w}
    {xs front back : List (Word w)} {entry caller : State w}
    (hp : Pre heapLimit base scratch xs entry)
    (hs : Stage heapLimit base scratch xs front back entry caller) :
    ∃ workspace, Combine.Pre heapLimit base scratch front back workspace caller := by
  have hsum : front.length + back.length = xs.length := by
    rw [hs.front_length, hs.back_length]
    exact Nat.add_sub_of_le (Nat.div_le_self _ _)
  obtain ⟨workspace, hn, ha⟩ := hs.scratch_array
  refine ⟨workspace, hs.source_array, ha, hn.trans hsum.symm, ?_,
    hs.source_reg, hs.scratch_reg, hs.length_reg.trans hsum.symm, ?_⟩
  · simpa only [hsum] using hp.disjoint
  · exact hs.split_reg.trans hs.front_length.symm

theorem after_combine {heapLimit : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry caller finish : State w}
    (_hp : Pre heapLimit base scratch xs entry)
    (hs : Stage heapLimit base scratch xs (sorted (xs.take (xs.length / 2)))
      (sorted (xs.drop (xs.length / 2))) entry caller)
    (hc : Combine.Post heapLimit base scratch (sorted (xs.take (xs.length / 2)))
      (sorted (xs.drop (xs.length / 2))) caller finish) :
    Post heapLimit base scratch xs entry finish := by
  have hsum : (sorted (xs.take (xs.length / 2))).length +
      (sorted (xs.drop (xs.length / 2))).length = xs.length := by
    rw [hs.front_length, hs.back_length]
    exact Nat.add_sub_of_le (Nat.div_le_self _ _)
  refine ⟨?_, ?_, ?_, hc.input.trans hs.input, hc.output.trans hs.output⟩
  · simpa only [merge_sorted_split] using hc.source_array
  · exact ⟨sorted xs, length_sorted xs,
      by simpa only [merge_sorted_split] using hc.scratch_array⟩
  · exact hs.frame.trans (by simpa only [hsum] using hc.frame)

theorem small_post {heapLimit : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry : State w} (hp : Pre heapLimit base scratch xs entry)
    (hsmall : xs.length ≤ 1) : Post heapLimit base scratch xs entry entry := by
  exact ⟨by simpa only [sorted_eq_self_of_length_le_one hsmall] using hp.source_array,
    hp.scratch_array, TwoBufferFrame.refl _ _ _ _ _, rfl, rfl⟩

end Ram.Source.Array.MergeSort
