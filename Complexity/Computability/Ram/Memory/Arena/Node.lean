/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Verification.Time.StraightLine

/-!
# Three-word node allocation

The existing source IR loads the shared cursor, reserves three words and stores
the supplied head, option tag and tail address individually. Only the returned
base register is assigned. The three input registers may coincide when their
actual words coincide; none may alias the destination register.

The endpoint is the exact sequence of state updates performed by this block,
not another evaluator. Its count comes from the existing local-frame compiler's
straight-line execution theorem. Source-node typing, valid links, outer option
construction and call/setup costs belong to the caller's separate contract.
-/

namespace Ram.Source.Arena.Node

/-- One returned base and three read-only input words. Input slots may coincide. -/
structure Registers where
  base : Reg
  head : Reg
  tag : Reg
  tail : Reg
  base_ne_head : base ≠ head
  base_ne_tag : base ≠ tag
  base_ne_tail : base ≠ tail

namespace Registers

/-- Reserve and initialize the actual head, tag and tail-address words. -/
def allocate (r : Registers) : Stmt :=
  .seq (.assign r.base (.load (.const 0)))
    (.seq (.store (.const 0) (.bin .add (.var r.base) (.const 3)))
      (.seq (.store (.var r.base) (.var r.head))
        (.seq (.store (.bin .add (.var r.base) (.const 1)) (.var r.tag))
          (.store (.bin .add (.var r.base) (.const 2)) (.var r.tail)))))

/-- The precise endpoint of the load, reservation and three initialization stores. -/
def appended (r : Registers) (s : State w) : State w :=
  ((((s.setReg r.base (s.mem 0)).setMem 0 (arrayAddr (s.mem 0) 3)).setMem
    (arrayAddr (s.mem 0) 0) (s.regs r.head)).setMem
      (arrayAddr (s.mem 0) 1) (s.regs r.tag)).setMem
        (arrayAddr (s.mem 0) 2) (s.regs r.tail)

/-- Node allocation has no branch, loop or function call. -/
theorem allocate_isStraightLine (r : Registers) : r.allocate.IsStraightLine := by
  simp [allocate, Stmt.IsStraightLine]

/-- Actual cursor and input words, with room for the complete three-word object. -/
structure Pre (r : Registers) (heapLimit : Nat)
    (base headValue tagValue tailValue : Word w) (entry : State w) : Prop where
  cursor : entry.mem 0 = base
  head_reg : entry.regs r.head = headValue
  tag_reg : entry.regs r.tag = tagValue
  tail_reg : entry.regs r.tail = tailValue
  positive : 0 < base.toNat
  capacity : base.toNat + 3 ≤ heapLimit
  fits : heapLimit < 2 ^ w

/-- All three supplied words are initialized; only the cursor, fresh interval
and returned-base register can change. -/
structure Post (r : Registers) (heapLimit : Nat)
    (base headValue tagValue tailValue : Word w) (entry finish : State w) : Prop where
  cursor : finish.mem 0 = arrayAddr base 3
  array : ArrayAt heapLimit base [headValue, tagValue, tailValue] finish
  base_reg : finish.regs r.base = base
  frame : ∀ address, address ≠ 0 →
    address.toNat < base.toNat ∨ base.toNat + 3 ≤ address.toNat →
    finish.mem address = entry.mem address
  other : ∀ slot, slot ≠ r.base → finish.regs slot = entry.regs slot
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev

/-- The five actual source statements execute safely with the stated capacity. -/
theorem allocate_safe (r : Registers) {program : Program} {heapLimit depth : Nat}
    {base headValue tagValue tailValue : Word w} {entry : State w}
    (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    SafeExec program heapLimit depth r.allocate entry (r.appended entry) := by
  have positive : 0 < heapLimit := by have capacity := pre.capacity; omega
  have baseBelow : base.toNat < heapLimit := by have capacity := pre.capacity; omega
  have addressBelow (index : Nat) (bound : index < 3) :
      (arrayAddr base index).toNat < heapLimit := by
    have capacity := pre.capacity
    have fits := pre.fits
    rw [arrayAddr_toNat (by omega)]
    omega
  have loaded : entry.eval (.load (.const 0)) = base := by
    change entry.mem (0 : Word w) = base
    exact pre.cursor
  have loadExecution : SafeExec program heapLimit depth
      (.assign r.base (.load (.const 0))) entry (entry.setReg r.base base) := by
    have execution := SafeExec.assign (program := program) (heapLimit := heapLimit)
      (d := depth) (s := entry) (dst := r.base) (value := .load (.const 0))
      ⟨trivial, by simpa using positive⟩
    simpa only [loaded] using execution
  have execution := SafeExec.seq
    loadExecution
    (SafeExec.seq
      (SafeExec.store (address := .const 0)
        (value := .bin .add (.var r.base) (.const 3))
        trivial ⟨trivial, trivial⟩ (by simpa using positive))
      (SafeExec.seq
        (SafeExec.store (address := .var r.base) (value := .var r.head)
          trivial trivial (by
            simpa [State.eval, Expr.eval, State.setReg, State.setMem]
              using baseBelow))
        (SafeExec.seq
          (SafeExec.store (address := .bin .add (.var r.base) (.const 1))
            (value := .var r.tag) ⟨trivial, trivial⟩ trivial (by
              simpa [State.eval, Expr.eval, BinOp.eval, State.setReg, State.setMem,
                arrayAddr] using addressBelow 1 (by decide)))
          (SafeExec.store (address := .bin .add (.var r.base) (.const 2))
            (value := .var r.tail) ⟨trivial, trivial⟩ trivial (by
              simpa [State.eval, Expr.eval, BinOp.eval, State.setReg, State.setMem,
                arrayAddr] using addressBelow 2 (by decide))))))
  unfold appended
  rw [pre.cursor]
  simpa [allocate, State.eval, Expr.eval, BinOp.eval, State.setReg,
    State.setMem, arrayAddr, Ne.symm r.base_ne_head, Ne.symm r.base_ne_tag,
    Ne.symm r.base_ne_tail] using execution

/-- The exact endpoint contains the heterogeneous node words and retains the
whole surrounding memory, all other locals and both streams. -/
theorem appended_post (r : Registers) {heapLimit : Nat}
    {base headValue tagValue tailValue : Word w} {entry : State w}
    (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    r.Post heapLimit base headValue tagValue tailValue entry (r.appended entry) := by
  unfold appended
  rw [pre.cursor, pre.head_reg, pre.tag_reg, pre.tail_reg]
  have addressValue (index : Nat) (bound : index < 3) :
      (arrayAddr base index).toNat = base.toNat + index := by
    have capacity := pre.capacity
    have fits := pre.fits
    exact arrayAddr_toNat (by omega)
  have nonzero (index : Nat) (bound : index < 3) : arrayAddr base index ≠ 0 := by
    intro same
    have zeroValue : (arrayAddr base index).toNat = 0 :=
      (Word.toNat_eq_zero_iff _).mpr same
    have value := addressValue index bound
    have positive := pre.positive
    omega
  have distinct (i j : Nat) (hi : i < 3) (hj : j < 3) (different : i ≠ j) :
      arrayAddr base i ≠ arrayAddr base j := by
    intro same
    have equal : (arrayAddr base i).toNat = (arrayAddr base j).toNat :=
      congrArg (fun address : Word w => address.toNat) same
    rw [addressValue i hi, addressValue j hj] at equal
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [State.setMem, State.setReg]
    rw [if_neg (Ne.symm (nonzero 2 (by decide))),
      if_neg (Ne.symm (nonzero 1 (by decide))),
      if_neg (Ne.symm (nonzero 0 (by decide)))]
    rfl
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using Nat.le_trans pre.capacity (Nat.le_of_lt pre.fits)
    · intro index bound
      have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 := by
        simp only [List.length_cons, List.length_nil] at bound
        omega
      rcases casesIndex with rfl | rfl | rfl
      · simp only [State.setMem, State.setReg]
        simp [distinct 0 1 (by decide) (by decide) (by decide),
          distinct 0 2 (by decide) (by decide) (by decide)]
      · simp only [State.setMem, State.setReg]
        simp [distinct 1 2 (by decide) (by decide) (by decide)]
      · simp [State.setMem, State.setReg]
    · simpa using pre.capacity
  · exact State.setReg_same entry r.base base
  · intro address nonzeroAddress outside
    have away (index : Nat) (bound : index < 3) : address ≠ arrayAddr base index := by
      intro same
      have value := addressValue index bound
      rw [← same] at value
      rcases outside with below | above <;> omega
    simp only [State.setMem, State.setReg]
    simp only [if_neg (away 0 (by decide)),
      if_neg (away 1 (by decide)), if_neg (away 2 (by decide))]
    exact if_neg nonzeroAddress
  · intro slot different
    simp [State.setReg, State.setMem, different]

/-- The existing compiler emits twenty-one instructions for this allocation block. -/
theorem allocate_stmtSize (r : Registers) (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable r.allocate = 21 := rfl

/-- The node body has exactly the count emitted by the existing local-frame
compiler. This excludes the caller's argument setup, return and outer tags. -/
theorem allocate_measured (r : Registers) {program : Program}
    {control heapLimit depth : Nat} {base headValue tagValue tailValue : Word w}
    {entry : State w} (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    ∃ finish, LocalMeasuredExec control program heapLimit depth r.allocate
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) r.allocate)
      entry finish ∧ r.Post heapLimit base headValue tagValue tailValue entry finish := by
  obtain ⟨steps, execution⟩ :=
    (r.allocate_safe (program := program) (depth := depth) pre).exists_localMeasured control
  have count := execution.steps_eq_stmtSize r.allocate_isStraightLine
  refine ⟨r.appended entry, ?_, r.appended_post pre⟩
  simpa only [count] using execution

end Registers

/-- The inline node allocator uses one returned base and three fresh operand
slots. The continuation keeps all four slots outside its new scratch region. -/
def inlineRegisters (next : Reg) : Registers where
  base := next
  head := next + 1
  tag := next + 2
  tail := next + 3
  base_ne_head := Nat.ne_of_lt (Nat.lt_succ_self next)
  base_ne_tag := Nat.ne_of_lt
    (Nat.lt_trans (Nat.lt_succ_self next) (Nat.lt_succ_self (next + 1)))
  base_ne_tail := Nat.ne_of_lt
    (Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self next) (Nat.lt_succ_self (next + 1)))
      (Nat.lt_succ_self (next + 2)))

end Ram.Source.Arena.Node
