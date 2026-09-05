import Ram.Contracts

/-!
# An input/output array-fill program verified with contracts

The fixed program reads a length, fills that many heap words with one, and
outputs the length. The loop proof uses the public invariant/potential rule;
it does not construct an execution derivation separately for each input.

The contracts use the optimized local-frame compiler and its measured execution
judgment. The linear budget is derived from that pipeline's generated
instructions. The final checked-compiler theorems give actual halted machine
execution and matching output. The heap-preserving interface additionally
transfers the filled-prefix assertion to the target machine's own memory,
using the explicit address bound.
-/

namespace Ram.Examples.ContractFill

open Source

def condition : Expr := .var 0
def nextPointer : Expr := .bin .add (.var 1) (.const 1)
def nextCount : Expr := .bin .sub (.var 0) (.const 1)

def body : Stmt :=
  .seq (.store (.var 1) (.const 1))
    (.seq (.assign 1 nextPointer) (.assign 0 nextCount))

def loop : Stmt := .while condition body

/-- One fixed program for every length and every admissible word width. -/
def main : Stmt :=
  .seq (.read 0)
    (.seq (.assign 1 (.const 0)) (.seq loop (.write (.var 1))))

def stored (s : Source.State w) : Source.State w := s.setMem (s.regs 1) 1
def advanced (s : Source.State w) : Source.State w :=
  (stored s).setReg 1 (s.regs 1 + 1)
def bodyResult (s : Source.State w) : Source.State w :=
  (advanced s).setReg 0 (s.regs 0 - 1)

@[simp] theorem bodyResult_pointer (s : Source.State w) :
    (bodyResult s).regs 1 = s.regs 1 + 1 := by
  simp [bodyResult, advanced, Source.State.setReg]

@[simp] theorem bodyResult_count (s : Source.State w) :
    (bodyResult s).regs 0 = s.regs 0 - 1 := by
  simp [bodyResult, Source.State.setReg]

@[simp] theorem bodyResult_mem (s : Source.State w) (a : Word w) :
    (bodyResult s).mem a = if a = s.regs 1 then 1 else s.mem a := rfl

@[simp] theorem bodyResult_input (s : Source.State w) :
    (bodyResult s).input = s.input := rfl

@[simp] theorem bodyResult_outputRev (s : Source.State w) :
    (bodyResult s).outputRev = s.outputRev := rfl

/-- The pointer marks the filled prefix; pointer plus remaining count is the
original logical length. These are ghost assertions, not runtime operations. -/
def Invariant (len : Nat) (s : Source.State w) : Prop :=
  (s.regs 1).toNat + (s.regs 0).toNat = len ∧
  (∀ i, i < (s.regs 1).toNat → s.mem (BitVec.ofNat w i) = 1) ∧
  s.input = [] ∧ s.outputRev = []

def remaining (s : Source.State w) : Nat := 14 * (s.regs 0).toNat + 2

def Post (len : Nat) (s : Source.State w) : Prop :=
  (∀ i, i < len → s.mem (BitVec.ofNat w i) = 1) ∧
  s.output = [BitVec.ofNat w len] ∧ s.input = []

theorem store_code_size :
    LocalCompiler.stmtSize 2 (LocalCompiler.calleeLocals [])
      (.store (.var 1) (.const 1)) = 3 := rfl
theorem pointer_code_size :
    LocalCompiler.stmtSize 2 (LocalCompiler.calleeLocals []) (.assign 1 nextPointer) = 4 := rfl
theorem count_code_size :
    LocalCompiler.stmtSize 2 (LocalCompiler.calleeLocals []) (.assign 0 nextCount) = 4 := rfl
theorem condition_code_size : (condition.compile (ABI.scratch 2)).length = 1 := rfl

/-- Three ordinary primitive contracts compose into the exact state
transformer and an eleven-transition budget. -/
theorem body_contract {H depth : Nat} (s : Source.State w)
    (haddr : (s.regs 1).toNat < H) :
    Contract 2 [] H depth body (fun t => t = s)
      (fun t => t = bodyResult s) (fun _ => 11) := by
  have hs : Contract 2 [] H depth (.store (.var 1) (.const 1))
      (fun t => t = s) (fun t => t = stored s) (fun _ => 3) := by
    apply Contract.store
    · intro t ht
      trivial
    · intro t ht
      trivial
    · intro t ht
      subst t
      exact haddr
    · intro t ht
      subst t
      rfl
  have hp : Contract 2 [] H depth (.assign 1 nextPointer)
      (fun t => t = stored s) (fun t => t = advanced s) (fun _ => 4) := by
    apply Contract.assign
    · intro t ht
      exact ⟨trivial, trivial⟩
    · intro t ht
      subst t
      rfl
  have hc : Contract 2 [] H depth (.assign 0 nextCount)
      (fun t => t = advanced s) (fun t => t = bodyResult s) (fun _ => 4) := by
    apply Contract.assign
    · intro t ht
      exact ⟨trivial, trivial⟩
    · intro t ht
      subst t
      rfl
  exact hs.seq_const (hp.seq_const hc)

theorem bodyResult_preserves {H len : Nat} (hw : 0 < w)
    (hlen : len ≤ H) (hfit : H < 2 ^ w) (s : Source.State w)
    (hs : Invariant len s) (hz : s.eval condition ≠ 0) :
    Invariant len (bodyResult s) ∧ remaining (bodyResult s) + 14 ≤ remaining s := by
  obtain ⟨hsum, hprefix, hin, hout⟩ := hs
  have hpos : 0 < (s.regs 0).toNat := by
    have hn : (s.regs 0).toNat ≠ 0 := by
      intro he
      exact hz ((Word.toNat_eq_zero_iff _).mp he)
    omega
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hptrfit : (s.regs 1).toNat + (1 : Word w).toNat < 2 ^ w := by
    rw [hone]
    omega
  have hptr : ((bodyResult s).regs 1).toNat = (s.regs 1).toNat + 1 := by
    rw [bodyResult_pointer, BitVec.toNat_add_of_lt hptrfit, hone]
  have hcount : ((bodyResult s).regs 0).toNat = (s.regs 0).toNat - 1 := by
    rw [bodyResult_count]
    change (BinOp.eval .sub (s.regs 0) 1).toNat = (s.regs 0).toNat - 1
    rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hone]; omega), hone]
  refine ⟨⟨?_, ?_, hin, hout⟩, ?_⟩
  · rw [hptr, hcount]
    omega
  · intro i hi
    rw [hptr] at hi
    by_cases he : i = (s.regs 1).toNat
    · rw [bodyResult_mem, he, Word.ofNat_toNat_self]
      simp
    · have hlt : i < (s.regs 1).toNat := by omega
      have hne : BitVec.ofNat w i ≠ s.regs 1 := by
        intro heq
        have heq' := congrArg BitVec.toNat heq
        rw [Word.ofNat_toNat_of_lt (by omega)] at heq'
        omega
      rw [bodyResult_mem, if_neg hne]
      exact hprefix i hlt
  · simp only [remaining, hcount]
    omega

/-- Invariant preservation and decreasing remaining budget establish both
termination and a linear bound, through the public loop contract rule. -/
theorem loop_contract {H len : Nat} (hw : 0 < w)
    (hlen : len ≤ H) (hfit : H < 2 ^ w) :
    Contract (w := w) 2 [] H 0 loop (Invariant len)
      (fun t => Invariant len t ∧ t.eval condition = 0) remaining := by
  apply Contract.while_contract (Invariant len) remaining (fun _ => 11)
  · intro s hs
    trivial
  · intro s hs hz
    change 1 + 1 ≤ 14 * (s.regs 0).toNat + 2
    omega
  · intro s hs hz
    have hpos : 0 < (s.regs 0).toNat := by
      have hn : (s.regs 0).toNat ≠ 0 := by
        intro he
        exact hz ((Word.toNat_eq_zero_iff _).mp he)
      omega
    have haddr : (s.regs 1).toNat < H := by
      have hsum := hs.1
      omega
    have hnext := bodyResult_preserves hw hlen hfit s hs hz
    apply (body_contract s haddr).mono_post
    intro t ht
    subst t
    refine ⟨hnext.1, ?_⟩
    change 1 + 1 + 11 + 1 + remaining (bodyResult s) ≤ remaining s
    omega

def InputReady (len : Nat) (s : Source.State w) : Prop :=
  s.input = [BitVec.ofNat w len] ∧ s.outputRev = []

def CountReady (len : Nat) (s : Source.State w) : Prop :=
  (s.regs 0).toNat = len ∧ s.input = [] ∧ s.outputRev = []

/-- Full source application: input read, pointer initialization, fill loop,
and output write, all included in the proved budget. -/
theorem main_contract {H len : Nat} (hw : 0 < w)
    (hlen : len ≤ H) (hfit : H < 2 ^ w) :
    Contract (w := w) 2 [] H 0 main (InputReady len) (Post len) (fun _ => 14 * len + 7) := by
  have hlenfit : len < 2 ^ w := Nat.lt_of_le_of_lt hlen hfit
  have hr : Contract (w := w) 2 [] H 0 (.read 0) (InputReady len)
      (CountReady len) (fun _ => 1) := by
    apply Contract.read
    intro s hs
    refine ⟨BitVec.ofNat w len, [], hs.1, ?_⟩
    exact ⟨by simpa using Word.ofNat_toNat_of_lt hlenfit, rfl, hs.2⟩
  have hi : Contract (w := w) 2 [] H 0 (.assign 1 (.const 0)) (CountReady len)
      (Invariant len) (fun _ => 2) := by
    apply Contract.assign
    · intro s hs
      trivial
    · intro s hs
      refine ⟨?_, ?_, hs.2.1, hs.2.2⟩
      · simpa [Source.State.setReg, Source.State.eval, Expr.eval] using hs.1
      · intro i hi
        simp [Source.State.setReg, Source.State.eval, Expr.eval] at hi
  have hl : Contract (w := w) 2 [] H 0 loop (Invariant len)
      (fun t => Invariant len t ∧ t.eval condition = 0) (fun _ => 14 * len + 2) := by
    apply (loop_contract hw hlen hfit).mono_budget
    intro s hs
    have hsum := hs.1
    dsimp [remaining]
    omega
  have ho : Contract (w := w) 2 [] H 0 (.write (.var 1))
      (fun t => Invariant len t ∧ t.eval condition = 0) (Post len) (fun _ => 2) := by
    apply Contract.write
    · intro s hs
      trivial
    · intro s hs
      have hzero : (s.regs 0).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hs.2
      have hptr : (s.regs 1).toNat = len := by
        have hsum := hs.1.1
        omega
      have hword : s.regs 1 = BitVec.ofNat w len := by
        rw [← hptr, Word.ofNat_toNat_self]
      refine ⟨?_, ?_, hs.1.2.2.1⟩
      · intro i hi
        exact hs.1.2.1 i (by omega)
      · simp [Source.State.output, Source.State.eval, Expr.eval, hs.1.2.2.2, hword]
  have hall := hr.seq_const (hi.seq_const (hl.seq_const ho))
  apply hall.mono_budget
  intro s hs
  omega

def machine : Code := LocalCompiler.rawLink 2 [] main

theorem main_valid : LocalCompiler.Valid 2 [] main := by
  refine ⟨?_, ?_, ?_⟩
  · simp [main, loop, body, condition, nextPointer, nextCount,
      Stmt.WellFormed, Expr.Bounded]
  · simp [main, loop, body, Compiler.CallsValid]
  · simp

theorem checked_machine : LocalCompiler.compileChecked 2 [] main = some machine :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨main_valid, rfl⟩

theorem machine_code_size : machine.length = 21 := rfl

/-- Checked compilation executes this same fixed application in at most
`14 * len + 9` real RAM transitions, including its prologue and halt. -/
theorem machine_correct {H len : Nat} (hw : 0 < w)
    (hlen : len ≤ H) (hfit : H < 2 ^ w) (hcodefit : machine.length < 2 ^ w) :
    ∃ sourceFinal : Source.State w, ∃ targetFinal : Ram.State w,
      Post len sourceFinal ∧
      Ram.TerminatesWithin machine (14 * len + 9)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w len]) targetFinal ∧
      targetFinal.output = [BitVec.ofNat w len] ∧ targetFinal.input = [] := by
  obtain ⟨sf, tf, hp, ht, ho, hi⟩ := (main_contract hw hlen hfit).compile
    (input := [BitVec.ofNat w len]) checked_machine hcodefit
    (by simpa using hfit) ⟨rfl, rfl⟩
  refine ⟨sf, tf, hp, ?_, ho.trans hp.2.1, hi.trans hp.2.2⟩
  simpa only [Nat.add_assoc] using ht

/-- The compiled machine itself fills the array, not merely its source model.
Every observed address is proved to lie in the source heap represented by the
compiler's heap correspondence. The runtime bound still counts the complete
execution, including input, output, prologue, and halt. -/
theorem machine_heap_correct {H len : Nat} (hw : 0 < w)
    (hlen : len ≤ H) (hfit : H < 2 ^ w) (hcodefit : machine.length < 2 ^ w) :
    ∃ targetFinal : Ram.State w,
      Ram.TerminatesWithin machine (14 * len + 9)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w len]) targetFinal ∧
      (∀ i, i < len → targetFinal.mem (BitVec.ofNat w i) = 1) ∧
      targetFinal.output = [BitVec.ofNat w len] ∧ targetFinal.input = [] := by
  obtain ⟨sf, tf, hp, ht, hheap, ho, hi⟩ := (main_contract hw hlen hfit).compile_heap
    (input := [BitVec.ofNat w len]) checked_machine hcodefit
    (by simpa using hfit) ⟨rfl, rfl⟩
  refine ⟨tf, ?_, ?_, ho.trans hp.2.1, hi.trans hp.2.2⟩
  · simpa only [Nat.add_assoc] using ht
  · intro i hi
    have hiH : i < H := Nat.lt_of_lt_of_le hi hlen
    have haddress : (BitVec.ofNat w i).toNat < H := by
      rw [Word.ofNat_toNat_of_lt (Nat.lt_trans hiH hfit)]
      exact hiH
    exact (hheap (BitVec.ofNat w i) haddress).symm.trans (hp.1 i hi)

end Ram.Examples.ContractFill
