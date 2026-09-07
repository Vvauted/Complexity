/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Amortized
import Ram.Tactic

/-!
# A real heap workload with amortized linear machine time

The input is a command count followed by Boolean words. One means push a cell
containing one; zero means clear, by visiting and zeroing every active cell.
The final stack height is written to output. The source program is fixed and
contains both loops: no command or heap operation is performed by the host.

The mathematical specification folds the commands over the stack height and
describes every heap cell below the declared boundary. Potential is ten times
the current height. It pays for expensive clear commands using credit retained
by earlier pushes. Budgets count actual compiled word-RAM transitions.
-/

namespace Ram.Examples.AmortizedClear

open Source

def push : Stmt :=
  .seq (.store (.var 1) (.const 1))
    (.assign 1 (.bin .add (.var 1) (.const 1)))

def clearBody : Stmt :=
  .seq (.assign 1 (.bin .sub (.var 1) (.const 1)))
    (.store (.var 1) (.const 0))

def clear : Stmt := .while (.var 1) clearBody

def command : Stmt := .ite (.var 2) push clear

def body : Stmt :=
  .seq (.read 2) (.seq command (.assign 0 (.bin .sub (.var 0) (.const 1))))

def loop : Stmt := .while (.var 0) body

def main : Stmt :=
  .seq (.read 0) (.seq (.assign 1 (.const 0)) (.seq loop (.write (.var 1))))

def advance (b : Bool) (top : Nat) : Nat := if b then top + 1 else 0

/-- Pure specification only; execution consumes the actual input words. -/
def result (commands : List Bool) (top : Nat) : Nat := commands.foldl (fun n b => advance b n) top

@[simp] theorem result_nil (top : Nat) : result [] top = top := rfl

@[simp] theorem result_cons (b : Bool) (rest : List Bool) (top : Nat) :
    result (b :: rest) top = result rest (advance b top) := rfl

theorem result_le (commands : List Bool) (top : Nat) :
    result commands top ≤ top + commands.length := by
  induction commands generalizing top with
  | nil => simp
  | cons b rest ih =>
      have h := ih (advance b top)
      rw [result_cons]
      cases b <;> simp only [advance, Bool.false_eq_true, if_false, if_true] at * <;>
        simp only [List.length_cons] <;> omega

def encode (commands : List Bool) : List (Word w) :=
  commands.map (fun b => if b then 1 else 0)

@[simp] theorem encode_nil : encode (w := w) [] = [] := rfl

@[simp] theorem encode_cons (b : Bool) (rest : List Bool) :
    encode (w := w) (b :: rest) = (if b then 1 else 0) :: encode rest := rfl

/-- Active cells contain one; all other allocated cells contain zero. -/
def Prefix (H top : Nat) (mem : Word w → Word w) : Prop :=
  ∀ i, i < H → mem (BitVec.ofNat w i) = if i < top then 1 else 0

private theorem ofNat_ne {i j : Nat} (hi : i < 2 ^ w) (hj : j < 2 ^ w)
    (hne : i ≠ j) : BitVec.ofNat w i ≠ BitVec.ofNat w j := by
  intro h
  apply hne
  have hnat := congrArg BitVec.toNat h
  simpa only [Word.ofNat_toNat_of_lt hi, Word.ofNat_toNat_of_lt hj] using hnat

theorem Prefix.push {H top : Nat} {mem : Word w → Word w}
    (h : Prefix H top mem) (hH : H < 2 ^ w) (htop : top < H) :
    Prefix H (top + 1)
      (fun a => if a = BitVec.ofNat w top then 1 else mem a) := by
  intro i hi
  by_cases heq : i = top
  · subst i
    simp
  · have hn := ofNat_ne (lt_trans hi hH) (lt_trans htop hH) heq
    simp only [if_neg hn, h i hi]
    have hc : i < top ↔ i < top + 1 := by omega
    simp only [hc]

theorem Prefix.pop {H top : Nat} {mem : Word w → Word w}
    (h : Prefix H top mem) (hH : H < 2 ^ w) (hpos : 0 < top) (htop : top ≤ H) :
    Prefix H (top - 1)
      (fun a => if a = BitVec.ofNat w (top - 1) then 0 else mem a) := by
  intro i hi
  by_cases heq : i = top - 1
  · subst i
    simp
  · have hn := ofNat_ne (lt_trans hi hH) (by omega) heq
    simp only [if_neg hn, h i hi]
    have hc : i < top ↔ i < top - 1 := by omega
    simp only [hc]

def pushResult (s : Source.State w) : Source.State w :=
  (s.setMem (s.regs 1) 1).setReg 1 (s.regs 1 + 1)

def popResult (s : Source.State w) : Source.State w :=
  let t := s.setReg 1 (s.regs 1 - 1)
  t.setMem (t.regs 1) 0

private theorem sub_one_nat (hw : 0 < w) (v : Word w) (hp : 0 < v.toNat) :
    (v - 1).toNat = v.toNat - 1 := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  change (BinOp.eval .sub v 1).toNat = _
  rw [BinOp.eval_sub_toNat_of_le v 1 (by omega), hone]

theorem push_contract {H depth : Nat} (s : Source.State w) (htop : (s.regs 1).toNat < H) :
    Contract 3 [] H depth push (fun t => t = s) (fun t => t = pushResult s)
      (fun _ => 7) := by
  ram_vc t ht [push, pushResult, ht, htop]

theorem pop_contract {H depth : Nat} (hw : 0 < w) (s : Source.State w)
    (hp : 0 < (s.regs 1).toNat) (htop : (s.regs 1).toNat ≤ H) :
    Contract 3 [] H depth clearBody (fun t => t = s) (fun t => t = popResult s)
      (fun _ => 7) := by
  have haddr : (s.regs 1 - 1).toNat < H := by rw [sub_one_nat hw _ hp]; omega
  ram_vc t ht [clearBody, popResult, ht, haddr]
  exact haddr

structure ClearInvariant (H : Nat) (entry s : Source.State w) : Prop where
  height : (s.regs 1).toNat ≤ (entry.regs 1).toNat
  heap : Prefix H (s.regs 1).toNat s.mem
  count : s.regs 0 = entry.regs 0
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

structure ClearPost (H : Nat) (entry s : Source.State w) : Prop where
  height : (s.regs 1).toNat = 0
  heap : Prefix H 0 s.mem
  count : s.regs 0 = entry.regs 0
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

/-- Clearing performs an actual store for each old cell, preserves the other
live state, and costs at most ten transitions per cell plus its final guard. -/
theorem clear_contract {H depth : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (entry : Source.State w) (htop : (entry.regs 1).toNat ≤ H)
    (hheap : Prefix H (entry.regs 1).toNat entry.mem) :
    Contract 3 [] H depth clear (fun s => s = entry) (ClearPost H entry)
      (fun _ => 10 * (entry.regs 1).toNat + 2) := by
  have hc : Contract 3 [] H depth clear (ClearInvariant H entry) (ClearPost H entry)
      (fun s => (s.regs 1).toNat * 10 + 2) := by
    apply Contract.while_linear_post (ClearInvariant H entry) (fun s => (s.regs 1).toNat) 7
    · intro s hs
      trivial
    · intro s hs hz
      have hp : 0 < (s.regs 1).toNat := by
        have hn : (s.regs 1).toNat ≠ 0 := fun h => hz ((Word.toNat_eq_zero_iff _).mp h)
        omega
      have hb : (s.regs 1).toNat ≤ H := hs.height.trans htop
      apply (pop_contract hw s hp hb).mono_post
      intro t ht
      subst t
      have hval : ((popResult s).regs 1).toNat = (s.regs 1).toNat - 1 := by
        change (s.regs 1 - 1).toNat = _
        exact sub_one_nat hw _ hp
      have hword : s.regs 1 - 1 = BitVec.ofNat w ((s.regs 1).toNat - 1) := by
        rw [← sub_one_nat hw _ hp, Word.ofNat_toNat_self]
      refine ⟨⟨?_, ?_, ?_, hs.input, hs.output⟩, ?_⟩
      · rw [hval]
        exact (Nat.sub_le _ _).trans hs.height
      · rw [hval]
        change Prefix H ((s.regs 1).toNat - 1)
          (fun a => if a = s.regs 1 - 1 then 0 else s.mem a)
        rw [hword]
        exact hs.heap.pop hH hp hb
      · simpa [popResult, Source.State.setReg, Source.State.setMem] using hs.count
      · rw [hval]
        omega
    · intro s hs hz
      have hv : (s.regs 1).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hz
      exact ⟨hv, by simpa only [hv] using hs.heap, hs.count, hs.input, hs.output⟩
  apply hc.consequence
  · intro s hs
    subst s
    exact ⟨Nat.le_refl _, hheap, rfl, rfl, rfl⟩
  · intro s hs
    exact hs
  · intro s hs
    subst s
    omega

structure CommandPost (H : Nat) (b : Bool) (entry s : Source.State w) : Prop where
  height : (s.regs 1).toNat = advance b (entry.regs 1).toNat
  heap : Prefix H (s.regs 1).toNat s.mem
  count : s.regs 0 = entry.regs 0
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

theorem pushResult_post {H : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (s : Source.State w) (htop : (s.regs 1).toNat < H)
    (hheap : Prefix H (s.regs 1).toNat s.mem) :
    CommandPost H true s (pushResult s) := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hfit : (s.regs 1).toNat + (1 : Word w).toNat < 2 ^ w := by omega
  have hv : ((pushResult s).regs 1).toNat = (s.regs 1).toNat + 1 := by
    change (s.regs 1 + 1).toNat = _
    rw [BitVec.toNat_add_of_lt hfit, hone]
  refine ⟨hv, ?_, ?_, rfl, rfl⟩
  · rw [hv]
    change Prefix H ((s.regs 1).toNat + 1)
      (fun a => if a = s.regs 1 then 1 else s.mem a)
    simpa only [Word.ofNat_toNat_self] using hheap.push hH htop
  · simp [pushResult, Source.State.setReg, Source.State.setMem]

/-- The branch budgets include the compiled conditional and its true-branch
skip jump; the potentially expensive clear is not charged a constant price. -/
theorem command_contract {H depth : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (b : Bool) (s : Source.State w) (hc : s.regs 2 = if b then 1 else 0)
    (htop : (s.regs 1).toNat < H) (hheap : Prefix H (s.regs 1).toNat s.mem) :
    Contract 3 [] H depth command (fun t => t = s) (CommandPost H b s)
      (fun _ => if b then 10 else 10 * (s.regs 1).toNat + 4) := by
  apply Verification.verify
  intro t ht
  subst t
  cases b with
  | false =>
      ram_vc [command, hc]
      apply Verification.WP.of_contract (clear_contract hw hH s (Nat.le_of_lt htop) hheap)
        rfl (by omega)
      intro t ht remaining hremaining
      exact ⟨ht.height, by simpa only [ht.height] using ht.heap,
        ht.count, ht.input, ht.output⟩
  | true =>
      have hone : (1 : Word w) ≠ 0 := by
        intro hz
        have hnat := congrArg BitVec.toNat hz
        simp [BitVec.toNat_one hw] at hnat
      ram_vc [command, hc, hone, Nat.ne_of_gt hw]
      apply Verification.WP.of_contract (push_contract s htop) rfl (by decide)
      intro t ht remaining hremaining
      subst t
      exact pushResult_post hw hH s htop hheap

def readState (b : Bool) (rest : List Bool) (s : Source.State w) : Source.State w :=
  { s.setReg 2 (if b then 1 else 0) with input := encode rest }

structure BodyPost (H : Nat) (b : Bool) (rest : List Bool) (entry s : Source.State w) : Prop where
  height : (s.regs 1).toNat = advance b (entry.regs 1).toNat
  heap : Prefix H (s.regs 1).toNat s.mem
  count : (s.regs 0).toNat = rest.length
  input : s.input = encode rest
  output : s.outputRev = entry.outputRev

/-- One command is read from the input stream, executed, and the actual
remaining-count register is decremented. The expensive bound depends on the
entry height, before it is converted into an amortized contract. -/
theorem body_contract {H depth : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (b : Bool) (rest : List Bool) (s : Source.State w)
    (hin : s.input = encode (b :: rest))
    (hcount : (s.regs 0).toNat = rest.length + 1)
    (htop : (s.regs 1).toNat < H) (hheap : Prefix H (s.regs 1).toNat s.mem) :
    Contract 3 [] H depth body (fun t => t = s) (BodyPost H b rest s)
      (fun _ => if b then 15 else 10 * (s.regs 1).toNat + 9) := by
  have hr : Contract 3 [] H depth (.read 2) (fun t => t = s)
      (fun t => t = readState b rest s) (fun _ => 1) := by
    ram_vc t ht [ht, hin, encode_cons, readState]
  have hc := command_contract (depth := depth) hw hH b (readState b rest s)
    (by simp [readState, Source.State.setReg])
    (by simpa [readState, Source.State.setReg] using htop)
    (by simpa [readState, Source.State.setReg] using hheap)
  have hd : Contract 3 [] H depth (.assign 0 (.bin .sub (.var 0) (.const 1)))
      (CommandPost H b (readState b rest s)) (BodyPost H b rest s) (fun _ => 4) := by
    apply Verification.verify
    intro t ht
    have hcount' : (t.regs 0).toNat = rest.length + 1 := by
      rw [ht.count]
      simpa [readState, Source.State.setReg] using hcount
    have hv : (t.regs 0 - 1).toNat = rest.length := by
      rw [sub_one_nat hw _ (by omega), hcount']
      omega
    have hp : BodyPost H b rest s (t.setReg 0 (t.regs 0 - 1)) := by
      refine ⟨?_, ?_, hv, ht.input, ht.output⟩
      · simpa [Source.State.setReg, readState] using ht.height
      · simpa [Source.State.setReg] using ht.heap
    ram_vc [hp]
    exact hp
  have h := hr.seq_const (hc.seq_const hd)
  apply h.mono_budget
  intro t ht
  cases b <;> simp [readState, Source.State.setReg]
  omega

structure Snapshot (H expected : Nat) (rest : List Bool) (s : Source.State w) : Prop where
  count : (s.regs 0).toNat = rest.length
  input : s.input = encode rest
  result : result rest (s.regs 1).toNat = expected
  capacity : (s.regs 1).toNat + rest.length ≤ H
  heap : Prefix H (s.regs 1).toNat s.mem
  output : s.outputRev = []

def Invariant (H expected : Nat) (s : Source.State w) : Prop :=
  ∃ rest, Snapshot H expected rest s

def potential (s : Source.State w) : Nat := 10 * (s.regs 1).toNat

/-- Expensive clear operations spend saved potential. The bound 25 is proved
from the two real execution bounds, not used as an instruction price. -/
theorem body_amortized {H depth : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (b : Bool) (rest : List Bool) (s : Source.State w)
    (hin : s.input = encode (b :: rest))
    (hcount : (s.regs 0).toNat = rest.length + 1)
    (htop : (s.regs 1).toNat < H) (hheap : Prefix H (s.regs 1).toNat s.mem) :
    AmortizedContract 3 [] H depth body (fun t => t = s)
      (fun _ t => BodyPost H b rest s t) potential (fun _ => 25) := by
  apply AmortizedContract.of_contract
    (bound := fun _ => if b then 15 else 10 * (s.regs 1).toNat + 9)
  · intro entry heq
    subst entry
    exact body_contract hw hH b rest s hin hcount htop hheap
  · intro entry t heq ht
    subst entry
    simp only [potential, ht.height]
    cases b <;> simp [advance] <;> omega

/-- The outer invariant records the unconsumed input and its abstract fold.
The rule retains final potential, allowing this workload to be composed with
another workload instead of silently throwing its saved credit away. -/
theorem loop_amortized {H depth expected : Nat} (hw : 0 < w) (hH : H < 2 ^ w) :
    AmortizedContract (w := w) 3 [] H depth loop (Invariant H expected)
      (fun _ t => Invariant H expected t ∧ t.eval (.var 0) = 0)
      potential (fun s => 28 * (s.regs 0).toNat + 2) := by
  have hl := AmortizedContract.while_linear (w := w) (control := 3) (program := [])
    (heapLimit := H) (depth := depth) (condition := .var 0) (body := body)
    (Invariant H expected) (fun s => (s.regs 0).toNat) potential 25
    (fun _ _ => True.intro)
  refine (hl ?_).mono_charge ?_
  · intro s hs hz
    obtain ⟨rest, hs⟩ := hs
    cases rest with
    | nil =>
        have hv : (s.regs 0).toNat = 0 := hs.count
        exact False.elim (hz ((Word.toNat_eq_zero_iff _).mp hv))
    | cons b rest =>
        have hc : (s.regs 0).toNat = rest.length + 1 := hs.count
        have hp : (s.regs 1).toNat < H := by
          have hcap := hs.capacity
          simp only [List.length_cons] at hcap
          omega
        apply (body_amortized hw hH b rest s hs.input hc hp hs.heap).mono_post
        intro entry t heq ht
        refine ⟨⟨rest, ?_⟩, ?_⟩
        · refine ⟨ht.count, ht.input, ?_, ?_, ht.heap, ht.output.trans hs.output⟩
          · rw [ht.height]
            exact hs.result
          · have hcap := hs.capacity
            rw [ht.height]
            cases b <;> simp [advance, List.length_cons] at * <;> omega
        · change (t.regs 0).toNat < (s.regs 0).toNat
          rw [ht.count, hc]
          omega
  · intro s hs
    change (s.regs 0).toNat * 28 + 2 ≤ 28 * (s.regs 0).toNat + 2
    omega

structure AnswerReady (H expected : Nat) (s : Source.State w) : Prop where
  height : (s.regs 1).toNat = expected
  heap : Prefix H expected s.mem
  input : s.input = []
  output : s.outputRev = []

/-- For an existing stack, initial credit is charged explicitly. In particular
this bound is linear in command count plus the initial stack height. -/
theorem loop_contract {H depth expected : Nat} (hw : 0 < w) (hH : H < 2 ^ w) :
    Contract (w := w) 3 [] H depth loop (Invariant H expected) (AnswerReady H expected)
      (fun s => 28 * (s.regs 0).toNat + 2 + 10 * (s.regs 1).toNat) := by
  apply (loop_amortized hw hH).toContract
  intro entry t hentry ht
  obtain ⟨rest, hs⟩ := ht.1
  have hz : (t.regs 0).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr ht.2
  have hr : rest = [] := by
    cases rest with
    | nil => rfl
    | cons b rest => have hc := hs.count; simp only [List.length_cons] at hc; omega
  subst rest
  have hv : (t.regs 1).toNat = expected := hs.result
  exact ⟨hv, by simpa only [hv] using hs.heap, hs.input, hs.output⟩

structure InputReady (H : Nat) (commands : List Bool) (s : Source.State w) : Prop where
  input : s.input = BitVec.ofNat w commands.length :: encode commands
  heap : Prefix H 0 s.mem
  output : s.outputRev = []

structure CountReady (H : Nat) (commands : List Bool) (s : Source.State w) : Prop where
  count : (s.regs 0).toNat = commands.length
  input : s.input = encode commands
  heap : Prefix H 0 s.mem
  output : s.outputRev = []

structure LoopReady (H : Nat) (commands : List Bool) (s : Source.State w) : Prop where
  count : (s.regs 0).toNat = commands.length
  height : (s.regs 1).toNat = 0
  invariant : Invariant H (result commands 0) s

structure Post (H : Nat) (commands : List Bool) (s : Source.State w) : Prop where
  output : s.output = [BitVec.ofNat w (result commands 0)]
  input : s.input = []
  heap : Prefix H (result commands 0) s.mem

/-- Input, initialization and output are ordinary charged source statements.
The initial heap is empty, so its potential is genuinely zero. -/
theorem main_contract {H depth : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (commands : List Bool) (hcap : commands.length ≤ H) :
    Contract (w := w) 3 [] H depth main (InputReady H commands) (Post H commands)
      (fun _ => 28 * commands.length + 7) := by
  have hcountFit : commands.length < 2 ^ w := lt_of_le_of_lt hcap hH
  have hr : Contract (w := w) 3 [] H depth (.read 0) (InputReady H commands)
      (CountReady H commands) (fun _ => 1) := by
    ram_vc s hs [hs.input]
    exact ⟨Word.ofNat_toNat_of_lt hcountFit, rfl, hs.heap, hs.output⟩
  have hi : Contract (w := w) 3 [] H depth (.assign 1 (.const 0)) (CountReady H commands)
      (LoopReady H commands) (fun _ => 2) := by
    apply Verification.verify
    intro s hs
    have hp : LoopReady H commands (s.setReg 1 0) := by
      refine ⟨?_, ?_, commands, ?_⟩
      · simpa [Source.State.setReg] using hs.count
      · simp [Source.State.setReg]
      · refine ⟨?_, hs.input, ?_, ?_, ?_, hs.output⟩
        · simpa [Source.State.setReg] using hs.count
        · simp [Source.State.setReg]
        · simpa [Source.State.setReg] using hcap
        · simpa [Source.State.setReg] using hs.heap
    ram_vc [hp]
    exact hp
  have hl : Contract (w := w) 3 [] H depth loop (LoopReady H commands)
      (AnswerReady H (result commands 0)) (fun _ => 28 * commands.length + 2) := by
    apply (loop_contract hw hH).consequence (fun _ hs => hs.invariant) (fun _ hs => hs)
    intro s hs
    rw [hs.count, hs.height]
  have ho : Contract (w := w) 3 [] H depth (.write (.var 1)) (AnswerReady H (result commands 0))
      (Post H commands) (fun _ => 2) := by
    apply Verification.verify
    intro s hs
    have hword : s.regs 1 = BitVec.ofNat w (result commands 0) := by
      rw [← hs.height, Word.ofNat_toNat_self]
    ram_vc [hs.input, hs.output, hword]
    exact ⟨rfl, rfl, hs.heap⟩
  have hc := hr.seq_const (hi.seq_const (hl.seq_const ho))
  apply hc.mono_budget
  intro s hs
  omega

def machine : Code := LocalCompiler.rawLink 3 [] main

theorem main_valid : LocalCompiler.Valid 3 [] main := by
  simp [LocalCompiler.Valid, Compiler.Valid, main, loop, body, command, push, clear, clearBody,
    Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]

theorem checked_machine : LocalCompiler.compileChecked 3 [] main = some machine :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨main_valid, rfl⟩

theorem machine_code_size : machine.length = 35 := rfl

/-- Full machine result, consumed input and functional heap correctness, with
an actual linear transition budget including boundary read and halt. Width
and capacity constrain the problem input, not an uncharged host computation. -/
theorem machine_correct {H : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (commands : List Bool) (hcap : commands.length ≤ H) (hcodefit : 35 < 2 ^ w) :
    ∃ finish,
      Ram.TerminatesWithin machine (28 * commands.length + 9)
        (Ram.State.initial
          (BitVec.ofNat w H :: BitVec.ofNat w commands.length :: encode commands)) finish ∧
      finish.output = [BitVec.ofNat w (result commands 0)] ∧ finish.input = [] ∧
      Prefix H (result commands 0) finish.mem := by
  have hc : machine.length < 2 ^ w := by rw [machine_code_size]; exact hcodefit
  have hs : H + 0 * ABI.frameSize 3 < 2 ^ w := by simpa using hH
  have hp : InputReady H commands
      (Source.State.initial (BitVec.ofNat w commands.length :: encode commands)) := by
    refine ⟨rfl, ?_, rfl⟩
    intro i hi
    simp [Source.State.initial]
  obtain ⟨sourceFinal, finish, hpost, ht, hmem, hout, hin⟩ :=
    (main_contract (depth := 0) hw hH commands hcap).compile_heap checked_machine hc hs hp
  refine ⟨finish, ?_, hout.trans hpost.output, hin.trans hpost.input, ?_⟩
  · simpa only [Nat.add_assoc] using ht
  · intro i hi
    rw [← hmem (BitVec.ofNat w i) (by rwa [Word.ofNat_toNat_of_lt (lt_trans hi hH)])]
    exact hpost.heap i hi

/-- The observable answer decodes to the natural fold, not just its residue.
The heap-capacity precondition also bounds every possible final stack height. -/
theorem machine_correct_decoded {H : Nat} (hw : 0 < w) (hH : H < 2 ^ w)
    (commands : List Bool) (hcap : commands.length ≤ H) (hcodefit : 35 < 2 ^ w) :
    ∃ finish,
      Ram.TerminatesWithin machine (28 * commands.length + 9)
        (Ram.State.initial
          (BitVec.ofNat w H :: BitVec.ofNat w commands.length :: encode commands)) finish ∧
      finish.output.map BitVec.toNat = [result commands 0] ∧ finish.input = [] ∧
      Prefix H (result commands 0) finish.mem := by
  obtain ⟨finish, ht, hout, hin, hheap⟩ := machine_correct hw hH commands hcap hcodefit
  have hresult : result commands 0 < 2 ^ w := by
    have h := result_le commands 0
    omega
  refine ⟨finish, ht, ?_, hin, hheap⟩
  rw [hout]
  simp only [List.map_cons, List.map_nil, Word.ofNat_toNat_of_lt hresult]

end Ram.Examples.AmortizedClear
