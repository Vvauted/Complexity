/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Slice
import Complexity.Computability.Ram.Verification.StateM.Traversal
import Complexity.Computability.Ram.Verification.Time.StraightLine

/-!
# Read-only array folds implemented by source expressions

`Fold.loop_safe` connects one fixed source-expression loop to ordinary
`List.foldl`. The loop updates its accumulator, advances a pointer and decreases
a remaining length. Its mathematical step is justified by an evaluation theorem
for the actual source expression, together with heap-read safety: it is not an
executable Lean callback supplied for free.

The cursor interface handles suffix views, address bounds and termination.
The fold theorem also preserves shared memory, input/output and unrelated locals.
A client invariant can retain read-only parameters used by the expression.
Separate measured theorems derive costs from that expression's generated code;
correctness and termination require no proposed time bound.
-/

namespace Ram.Source.Array.Fold

/-- The three writable local variables of a read-only scalar fold. -/
structure Registers where
  pointer : Reg
  remaining : Reg
  accumulator : Reg
  pointer_ne_remaining : pointer ≠ remaining
  pointer_ne_accumulator : pointer ≠ accumulator
  remaining_ne_accumulator : remaining ≠ accumulator

/-- One actual source iteration. Only `value` depends on the selected fold. -/
def body (registers : Registers) (value : Expr) : Stmt :=
  .seq (.assign registers.accumulator value)
    (.seq
      (.assign registers.pointer (.bin .add (.var registers.pointer) (.const 1)))
      (.assign registers.remaining (.bin .sub (.var registers.remaining) (.const 1))))

/-- The fixed guarded traversal of a preloaded array. -/
def loop (registers : Registers) (value : Expr) : Stmt :=
  .while (.var registers.remaining) (body registers value)

/-- The state reached by the three assignments of `body`. -/
def stepState (registers : Registers) (value : Expr) (s : State w) : State w :=
  let updated := s.setReg registers.accumulator (s.eval value)
  let advanced := updated.setReg registers.pointer (s.regs registers.pointer + 1)
  advanced.setReg registers.remaining (s.regs registers.remaining - 1)

@[simp] theorem stepState_pointer (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).regs registers.pointer = s.regs registers.pointer + 1 := by
  simp [stepState, State.setReg, registers.pointer_ne_remaining]

@[simp] theorem stepState_remaining (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).regs registers.remaining = s.regs registers.remaining - 1 := by
  simp [stepState, State.setReg]

@[simp] theorem stepState_accumulator (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).regs registers.accumulator = s.eval value := by
  simp [stepState, State.setReg, Ne.symm registers.pointer_ne_accumulator,
    Ne.symm registers.remaining_ne_accumulator]

@[simp] theorem stepState_mem (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).mem = s.mem := rfl

@[simp] theorem stepState_input (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).input = s.input := rfl

@[simp] theorem stepState_outputRev (registers : Registers) (value : Expr) (s : State w) :
    (stepState registers value s).outputRev = s.outputRev := rfl

/-- An additional read-only parameter survives the iteration automatically. -/
theorem stepState_other (registers : Registers) (value : Expr) (s : State w) {r : Reg}
    (hp : r ≠ registers.pointer) (hc : r ≠ registers.remaining)
    (ha : r ≠ registers.accumulator) :
    (stepState registers value s).regs r = s.regs r := by
  simp [stepState, State.setReg, hp, hc, ha]

private theorem body_state (registers : Registers) (value : Expr) (s : State w) :
    let a := s.setReg registers.accumulator (s.eval value)
    let b := a.setReg registers.pointer
      (a.eval (.bin .add (.var registers.pointer) (.const 1)))
    b.setReg registers.remaining
      (b.eval (.bin .sub (.var registers.remaining) (.const 1))) =
        stepState registers value s := by
  simp [stepState, State.eval, Expr.eval, BinOp.eval, State.setReg,
    registers.pointer_ne_accumulator, registers.remaining_ne_accumulator,
    Ne.symm registers.pointer_ne_remaining]

/-- The expression's real reads are the only heap accesses in one iteration. -/
theorem body_safe (registers : Registers) {value : Expr} {program : Program}
    {heapLimit depth : Nat} (s : State w)
    (reads : value.ReadsBelow heapLimit s.regs s.mem) :
    SafeExec program heapLimit depth (body registers value) s (stepState registers value s) := by
  rw [← body_state registers value s]
  exact .seq (.assign reads) (.seq (.assign ⟨trivial, trivial⟩) (.assign ⟨trivial, trivial⟩))

/-- Every successful body execution has this actual three-assignment state. -/
theorem body_result (registers : Registers) {value : Expr} {program : Program}
    {heapLimit depth : Nat} {s t : State w}
    (h : SafeExec program heapLimit depth (body registers value) s t) :
    t = stepState registers value s := by
  cases h with
  | seq first rest =>
      cases first with
      | assign _ =>
          cases rest with
          | seq second third =>
              cases second with
              | assign _ =>
                  cases third with
                  | assign _ => exact body_state registers value s

private theorem decrement_toNat (hw : 0 < w) (count : Word w) (hne : count ≠ 0) :
    (count - 1).toNat = count.toNat - 1 := by
  have hp : 0 < count.toNat :=
    Nat.pos_of_ne_zero (fun h => hne ((Word.toNat_eq_zero_iff _).mp h))
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hle : (1 : Word w).toNat ≤ count.toNat := by omega
  change (BinOp.eval .sub count 1).toNat = count.toNat - 1
  rw [BinOp.eval_sub_toNat_of_le _ _ hle, hone]

/-- The remaining length decreases as a natural number whenever the guard is true. -/
theorem stepState_remaining_toNat (registers : Registers) {value : Expr}
    (hw : 0 < w) (s : State w) (hne : s.regs registers.remaining ≠ 0) :
    ((stepState registers value s).regs registers.remaining).toNat =
      (s.regs registers.remaining).toNat - 1 := by
  rw [stepState_remaining, decrement_toNat hw _ hne]

/-- A non-wrapping read-only suffix together with its fixed final endpoint. -/
structure Cursor (registers : Registers) (heapLimit : Nat) (target : Word w)
    (remaining : List (Word w)) (s : State w) : Prop where
  array : ArrayAt heapLimit (s.regs registers.pointer) remaining s
  count : (s.regs registers.remaining).toNat = remaining.length
  fit : (s.regs registers.pointer).toNat + remaining.length < 2 ^ w
  endpoint : arrayAddr (s.regs registers.pointer) remaining.length = target

namespace Cursor

variable {registers : Registers} {heapLimit : Nat} {target x : Word w}
variable {xs : List (Word w)} {s t : State w}

/-- A nonempty suffix makes the runtime guard true. -/
theorem nonzero (h : Cursor registers heapLimit target (x :: xs) s) :
    s.regs registers.remaining ≠ 0 := by
  intro hz
  have hzero := (Word.toNat_eq_zero_iff (s.regs registers.remaining)).mpr hz
  rw [h.count] at hzero
  simp at hzero

/-- The represented head is the word loaded by the pointer expression. -/
theorem head (h : Cursor registers heapLimit target (x :: xs) s) :
    s.mem (s.regs registers.pointer) = x := by
  simpa [arrayAddr] using h.array.1.lookup 0 (by simp)

/-- A nonempty represented suffix justifies its actual next heap read. -/
theorem address_lt (h : Cursor registers heapLimit target (x :: xs) s) :
    (s.regs registers.pointer).toNat < heapLimit := by
  have := h.array.2
  simp only [List.length_cons] at this
  omega

/-- Cursor progress depends only on actual pointer/counter changes and unchanged
memory. A later verified call-based iteration can reuse the same suffix rule. -/
theorem advance (h : Cursor registers heapLimit target (x :: xs) s) (hw : 0 < w)
    (memory : t.mem = s.mem)
    (pointer : t.regs registers.pointer = s.regs registers.pointer + 1)
    (count : t.regs registers.remaining = s.regs registers.remaining - 1) :
    Cursor registers heapLimit target xs t := by
  have hnext : (s.regs registers.pointer + 1).toNat =
      (s.regs registers.pointer).toNat + 1 :=
    arrayAddr_toNat (base := s.regs registers.pointer) (i := 1)
      (by have := h.fit; simp only [List.length_cons] at this; omega)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [memory, pointer]
    simpa [arrayAddr] using h.array.1.drop 1
  · rw [pointer, hnext]
    have := h.array.2
    simp only [List.length_cons] at this
    omega
  · rw [count, decrement_toNat hw _ h.nonzero, h.count]
    simp
  · rw [pointer, hnext]
    have := h.fit
    simp only [List.length_cons] at this
    omega
  · rw [pointer]
    change arrayAddr (arrayAddr (s.regs registers.pointer) 1) xs.length = target
    rw [arrayAddr_add, Nat.add_comm 1 xs.length]
    exact h.endpoint

end Cursor

private structure LoopRep (registers : Registers) (heapLimit : Nat)
    (entry : State w) (target : Word w) (R : State w → Prop)
    (remaining : List (Word w)) (acc : Word w) (s : State w) : Prop where
  cursor : Cursor registers heapLimit target remaining s
  accumulator : s.regs registers.accumulator = acc
  invariant : R s
  memory : s.mem = entry.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
    r ≠ registers.accumulator → s.regs r = entry.regs r

private theorem body_refines (registers : Registers) {value : Expr} {program : Program}
    {heapLimit depth : Nat} {entry : State w} {target : Word w}
    {step : Word w → Word w → Word w} {R : State w → Prop} (hw : 0 < w)
    (reads : ∀ s, R s → (s.regs registers.pointer).toNat < heapLimit →
      value.ReadsBelow heapLimit s.regs s.mem)
    (eval : ∀ s, R s →
      s.eval value = step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer)))
    (preserve : ∀ s, R s → R (stepState registers value s))
    (x : Word w) (xs : List (Word w)) :
    Refines program heapLimit depth (body registers value)
      (LoopRep registers heapLimit entry target R (x :: xs))
      (fun result => LoopRep registers heapLimit entry target R xs result.2)
      (modify (fun acc => step acc x) : StateM (Word w) PUnit).run := by
  intro acc s represented
  refine ⟨stepState registers value s,
    body_safe registers s (reads s represented.invariant represented.cursor.address_lt), ?_⟩
  change LoopRep registers heapLimit entry target R xs (step acc x) _
  refine ⟨represented.cursor.advance hw rfl
      (stepState_pointer registers value s) (stepState_remaining registers value s),
    ?_, preserve s represented.invariant, represented.memory,
    represented.input, represented.output, ?_⟩
  · rw [stepState_accumulator, eval s represented.invariant,
      represented.accumulator, represented.cursor.head]
  · intro r hp hc ha
    exact (stepState_other registers value s hp hc ha).trans (represented.other r hp hc ha)

private theorem forM_modify_run (step : Word w → Word w → Word w)
    (xs : List (Word w)) (acc : Word w) :
    ((List.forM xs (fun x => modify (fun a => step a x)) :
      StateM (Word w) PUnit).run acc).2 = xs.foldl step acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      change ((List.forM xs (fun x => modify (fun a => step a x)) :
        StateM (Word w) PUnit).run (step acc x)).2 = xs.foldl step (step acc x)
      exact ih _

/-- Verify a read-only source-expression fold using ordinary `List.foldl`.
The expression's evaluation and memory safety are proved under `R`; `preserve`
retains any read-only parameters needed by that proof. Cursor progress,
termination, shared-state framing and preservation of unrelated locals are
provided by the library. The step function is a mathematical specification. -/
theorem loop_safe (registers : Registers) {value : Expr} {program : Program}
    {heapLimit depth : Nat} {step : Word w → Word w → Word w} {R : State w → Prop}
    (hw : 0 < w)
    (reads : ∀ s, R s → (s.regs registers.pointer).toNat < heapLimit →
      value.ReadsBelow heapLimit s.regs s.mem)
    (eval : ∀ s, R s →
      s.eval value = step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer)))
    (preserve : ∀ s, R s → R (stepState registers value s))
    (s : State w) (base : Word w) (xs : List (Word w)) (invariant : R s)
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit depth (loop registers value) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.regs registers.pointer = arrayAddr base xs.length ∧ t.regs registers.remaining = 0 ∧
      R t ∧ t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → t.regs r = s.regs r := by
  have traversal := Refines.stateM_forM
    (program := program) (heapLimit := heapLimit) (depth := depth)
    (condition := .var registers.remaining) (body := body registers value)
    (rep := LoopRep registers heapLimit s (arrayAddr base xs.length) R)
    (fun x : Word w => modify (fun acc => step acc x))
    (by intros; trivial)
    (by
      intro remaining acc current h
      change current.regs registers.remaining ≠ 0 ↔ remaining ≠ []
      apply not_congr
      exact (Word.toNat_eq_zero_iff (current.regs registers.remaining)).symm.trans
        (by rw [h.cursor.count]; exact List.length_eq_zero_iff))
    (body_refines registers hw reads eval preserve) xs
  have start : LoopRep registers heapLimit s (arrayAddr base xs.length) R
      xs (s.regs registers.accumulator) s :=
    ⟨⟨⟨by simpa only [pointer] using represented,
        by simpa only [pointer] using heap⟩, count,
        by simpa only [pointer] using fit, by rw [pointer]⟩,
      rfl, invariant, rfl, rfl, rfl, by intros; rfl⟩
  obtain ⟨t, execution, result⟩ := traversal (s.regs registers.accumulator) s start
  refine ⟨t, execution, result.accumulator.trans (forM_modify_run step xs _), ?_, ?_,
    result.invariant, result.memory, result.input, result.output, result.other⟩
  · simpa [arrayAddr] using result.cursor.endpoint
  · exact (Word.toNat_eq_zero_iff _).mp result.cursor.count


/-- The three assignments are straight-line code, independently of the expression. -/
theorem body_isStraightLine (registers : Registers) (value : Expr) :
    (body registers value).IsStraightLine := by
  simp [body, Stmt.IsStraightLine]

/-- Static iteration size is the actual expression code plus one result write
and the two pointer/counter assignment blocks. -/
theorem body_code_size (registers : Registers) (value : Expr)
    (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable (body registers value) =
      (value.compile (ABI.scratch control)).length + 9 := by
  simp [body, LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile]

/-- Every successful iteration has the count of its emitted straight-line code. -/
theorem body_localMeasured (registers : Registers) {value : Expr} {program : Program}
    {control heapLimit depth : Nat} {s t : State w}
    (h : SafeExec program heapLimit depth (body registers value) s t) :
    LocalMeasuredExec control program heapLimit depth (body registers value)
      ((value.compile (ABI.scratch control)).length + 9) s t := by
  obtain ⟨steps, measured⟩ := h.exists_localMeasured control
  have count := measured.steps_eq_stmtSize (body_isStraightLine registers value)
  rw [body_code_size] at count
  simpa only [count] using measured

/-- The runtime counter determines the actual number of emitted iterations.
The coefficient contains expression code, accumulator and cursor writes, guard
and backedge; the final false guard is included. No cost annotation is assumed. -/
theorem loop_localMeasured (registers : Registers) {value : Expr} {program : Program}
    {control heapLimit depth : Nat} (hw : 0 < w) {s t : State w}
    (h : SafeExec program heapLimit depth (loop registers value) s t) :
    LocalMeasuredExec control program heapLimit depth (loop registers value)
      (((value.compile (ABI.scratch control)).length + 12) *
        (s.regs registers.remaining).toNat + 2) s t := by
  generalize hc : (s.regs registers.remaining).toNat = count
  induction count using Nat.strongRecOn generalizing s t with
  | ind count ih =>
      cases h with
      | whileFalse reads hz =>
          have hzero : count = 0 := by
            rw [← hc]
            exact (Word.toNat_eq_zero_iff _).mpr hz
          have hrun : LocalMeasuredExec control program heapLimit depth
              (loop registers value) 2 s s := .whileFalse reads hz
          simpa only [hzero, Nat.mul_zero, Nat.zero_add] using hrun
      | whileTrue reads hz hb hr =>
          have hpos : 0 < (s.regs registers.remaining).toNat :=
            Nat.pos_of_ne_zero (fun he => hz ((Word.toNat_eq_zero_iff _).mp he))
          have hm := body_result registers hb
          cases hm
          have hcount' :
              ((stepState registers value s).regs registers.remaining).toNat =
                (s.regs registers.remaining).toNat - 1 :=
            stepState_remaining_toNat registers hw s hz
          have hlt : ((stepState registers value s).regs registers.remaining).toNat < count := by
            rw [hcount', ← hc]
            omega
          have hrest := ih _ hlt hr rfl
          have hrun : LocalMeasuredExec control program heapLimit depth (loop registers value)
              (1 + 1 + ((value.compile (ABI.scratch control)).length + 9) + 1 +
                (((value.compile (ABI.scratch control)).length + 12) *
                  ((stepState registers value s).regs registers.remaining).toNat + 2)) s t :=
            .whileTrue reads hz (body_localMeasured registers hb) hrest
          have hsteps :
              1 + 1 + ((value.compile (ABI.scratch control)).length + 9) + 1 +
                (((value.compile (ABI.scratch control)).length + 12) *
                  ((stepState registers value s).regs registers.remaining).toNat + 2) =
                ((value.compile (ABI.scratch control)).length + 12) * count + 2 := by
            rw [hcount', ← hc]
            calc
              _ = ((value.compile (ABI.scratch control)).length + 12) *
                    ((s.regs registers.remaining).toNat - 1) +
                    ((value.compile (ABI.scratch control)).length + 12) + 2 := by omega
              _ = ((value.compile (ABI.scratch control)).length + 12) *
                    ((s.regs registers.remaining).toNat - 1 + 1) + 2 := by
                  rw [Nat.mul_add, Nat.mul_one]
              _ = _ := by rw [Nat.sub_add_cancel hpos]
          simpa only [hsteps] using hrun

end Ram.Source.Array.Fold
