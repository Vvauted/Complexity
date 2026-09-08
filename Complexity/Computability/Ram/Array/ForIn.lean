/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Fold
import Complexity.Computability.Ram.Source.ForIn

/-!
# Read-only scalar folds through array iteration

The array iteration copies its pointer and remaining length, loads each element
into its own local and executes a fixed source body. With fresh cursor locals,
the original descriptor is not advanced; the generic rule gives the exact local
frame. An implemented scalar update connects this computation to ordinary
`List.foldl`; cursor progress and list traversal reuse the existing proof rules.

The element local is writable alongside the accumulator and two private cursor
locals. The frame theorem excludes all four, rather than claiming the last
loaded element is unchanged. Correctness requires no time bound. The separate
constant-body count includes cursor initialization, each load and cursor update,
and all loop guards and backedges.
-/

namespace Ram.Source.Array.ForIn

/-- The ordinary fold locals plus a separate current-element binding. -/
structure Registers extends Fold.Registers where
  element : Reg
  element_ne_pointer : element ≠ pointer
  element_ne_remaining : element ≠ remaining
  element_ne_accumulator : element ≠ accumulator

/-- State after the two actual cursor-initialization assignments. The length
expression is evaluated after the pointer assignment, exactly as in the source. -/
def initialState (registers : Registers) (base length : Expr) (s : State w) : State w :=
  let positioned := s.setReg registers.pointer (s.eval base)
  positioned.setReg registers.remaining (positioned.eval length)

@[simp] theorem initialState_pointer (registers : Registers) (base length : Expr)
    (s : State w) :
    (initialState registers base length s).regs registers.pointer = s.eval base := by
  simp [initialState, State.setReg, registers.pointer_ne_remaining]

@[simp] theorem initialState_remaining (registers : Registers) (base length : Expr)
    (s : State w) :
    (initialState registers base length s).regs registers.remaining =
      (s.setReg registers.pointer (s.eval base)).eval length := by
  simp [initialState, State.setReg]

@[simp] theorem initialState_accumulator (registers : Registers) (base length : Expr)
    (s : State w) :
    (initialState registers base length s).regs registers.accumulator =
      s.regs registers.accumulator := by
  simp [initialState, State.setReg, Ne.symm registers.pointer_ne_accumulator,
    Ne.symm registers.remaining_ne_accumulator]

/-- An iteration loads the head before storing its implemented accumulator
result and advancing the private cursor. This describes the real state changes. -/
def stepState (registers : Registers) (value : Word w) (s : State w) : State w :=
  Fold.advanceState registers.toRegisters value
    (s.setReg registers.element (s.mem (s.regs registers.pointer)))

@[simp] theorem stepState_pointer (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).regs registers.pointer = s.regs registers.pointer + 1 := by
  simp [stepState, State.setReg, Ne.symm registers.element_ne_pointer]

@[simp] theorem stepState_remaining (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).regs registers.remaining = s.regs registers.remaining - 1 := by
  simp [stepState, State.setReg, Ne.symm registers.element_ne_remaining]

@[simp] theorem stepState_accumulator (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).regs registers.accumulator = value :=
  Fold.advanceState_accumulator registers.toRegisters value _

@[simp] theorem stepState_mem (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).mem = s.mem := rfl

@[simp] theorem stepState_input (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).input = s.input := rfl

@[simp] theorem stepState_outputRev (registers : Registers) (value : Word w) (s : State w) :
    (stepState registers value s).outputRev = s.outputRev := rfl

/-- All four writable roles are excluded from the local-variable frame. -/
theorem stepState_other (registers : Registers) (value : Word w) (s : State w) {r : Reg}
    (hp : r ≠ registers.pointer) (hc : r ≠ registers.remaining)
    (ha : r ≠ registers.accumulator) (he : r ≠ registers.element) :
    (stepState registers value s).regs r = s.regs r := by
  rw [stepState, Fold.advanceState_other registers.toRegisters _ _ hp hc ha]
  simp [State.setReg, he]

private structure LoopRep (registers : Registers) (heapLimit : Nat)
    (entry : State w) (target : Word w) (R : State w → Prop)
    (remaining : List (Word w)) (accumulator : Word w) (s : State w) : Prop where
  cursor : Fold.Cursor registers.toRegisters heapLimit target remaining s
  accumulator : s.regs registers.accumulator = accumulator
  invariant : R s
  memory : s.mem = entry.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
    r ≠ registers.accumulator → r ≠ registers.element → s.regs r = entry.regs r

private theorem step_refines (registers : Registers) {iteration : Stmt} {program : Program}
    {heapLimit depth : Nat} {entry : State w} {target : Word w}
    {step : Word w → Word w → Word w} {R : State w → Prop} (hw : 0 < w)
    (implementation : ∀ s, R s → s.regs registers.remaining ≠ 0 →
      (s.regs registers.pointer).toNat < heapLimit →
      SafeExec program heapLimit depth iteration s
        (stepState registers
          (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (preserve : ∀ s, R s → s.regs registers.remaining ≠ 0 → R (stepState registers
      (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (x : Word w) (xs : List (Word w)) :
    Refines program heapLimit depth iteration
      (LoopRep registers heapLimit entry target R (x :: xs))
      (fun result => LoopRep registers heapLimit entry target R xs result.2)
      (modify (fun accumulator => step accumulator x) : StateM (Word w) PUnit).run := by
  intro accumulator s represented
  refine ⟨_, implementation s represented.invariant represented.cursor.nonzero
    represented.cursor.address_lt, ?_⟩
  change LoopRep registers heapLimit entry target R xs (step accumulator x) _
  refine ⟨represented.cursor.advance hw rfl
      (stepState_pointer registers _ s) (stepState_remaining registers _ s),
    ?_, preserve s represented.invariant represented.cursor.nonzero, represented.memory,
    represented.input, represented.output, ?_⟩
  · rw [stepState_accumulator, represented.accumulator, represented.cursor.head]
  · intro r hp hc ha he
    exact (stepState_other registers _ s hp hc ha he).trans (represented.other r hp hc ha he)

/-- Reuse the list-traversal rule on actual nonempty suffixes. The implementation
and invariant preservation are required only when the loop guard is true, not
at the unexecuted empty endpoint. The frame excludes the loaded element local. -/
theorem loop_safe_of_step_guarded (registers : Registers) {iteration : Stmt} {program : Program}
    {heapLimit depth : Nat} {step : Word w → Word w → Word w} {R : State w → Prop}
    (hw : 0 < w)
    (implementation : ∀ s, R s → s.regs registers.remaining ≠ 0 →
      (s.regs registers.pointer).toNat < heapLimit →
      SafeExec program heapLimit depth iteration s
        (stepState registers
          (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (preserve : ∀ s, R s → s.regs registers.remaining ≠ 0 → R (stepState registers
      (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (s : State w) (base : Word w) (xs : List (Word w)) (invariant : R s)
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit depth (.while (.var registers.remaining) iteration) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.regs registers.pointer = arrayAddr base xs.length ∧ t.regs registers.remaining = 0 ∧
      R t ∧ t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r := by
  have traversal := Refines.stateM_forM
    (program := program) (heapLimit := heapLimit) (depth := depth)
    (condition := .var registers.remaining) (body := iteration)
    (rep := LoopRep registers heapLimit s (arrayAddr base xs.length) R)
    (fun x : Word w => modify (fun accumulator => step accumulator x))
    (by intros; trivial)
    (by
      intro remaining accumulator current h
      change current.regs registers.remaining ≠ 0 ↔ remaining ≠ []
      apply not_congr
      exact (Word.toNat_eq_zero_iff (current.regs registers.remaining)).symm.trans
        (by rw [h.cursor.count]; exact List.length_eq_zero_iff))
    (step_refines registers hw implementation preserve) xs
  have start : LoopRep registers heapLimit s (arrayAddr base xs.length) R
      xs (s.regs registers.accumulator) s :=
    ⟨⟨⟨by simpa only [pointer] using represented,
        by simpa only [pointer] using heap⟩, count,
        by simpa only [pointer] using fit, by rw [pointer]⟩,
      rfl, invariant, rfl, rfl, rfl, by intros; rfl⟩
  obtain ⟨t, execution, result⟩ := traversal (s.regs registers.accumulator) s start
  refine ⟨t, execution, result.accumulator.trans (List.forM_modify_run step xs _), ?_, ?_,
    result.invariant, result.memory, result.input, result.output, result.other⟩
  · simpa [arrayAddr] using result.cursor.endpoint
  · exact (Word.toNat_eq_zero_iff _).mp result.cursor.count

/-- The unconditional step interface is a specialization of the guarded
traversal rule. Existing implementations need not mention the guard. -/
theorem loop_safe_of_step (registers : Registers) {iteration : Stmt} {program : Program}
    {heapLimit depth : Nat} {step : Word w → Word w → Word w} {R : State w → Prop}
    (hw : 0 < w)
    (implementation : ∀ s, R s → (s.regs registers.pointer).toNat < heapLimit →
      SafeExec program heapLimit depth iteration s
        (stepState registers
          (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (preserve : ∀ s, R s → R (stepState registers
      (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (s : State w) (base : Word w) (xs : List (Word w)) (invariant : R s)
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit depth (.while (.var registers.remaining) iteration) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.regs registers.pointer = arrayAddr base xs.length ∧ t.regs registers.remaining = 0 ∧
      R t ∧ t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r :=
  loop_safe_of_step_guarded registers hw (fun s h _ => implementation s h)
    (fun s h _ => preserve s h) s base xs invariant represented pointer count heap fit

/-- Load the actual next element, execute its implemented scalar update, then
reuse the existing cursor assignments. No list element is supplied for free. -/
theorem body_safe (registers : Registers) {body : Stmt} {program : Program}
    {heapLimit depth : Nat} {step : Word w → Word w → Word w} {R : State w → Prop}
    (implementation : ∀ current, R current →
      SafeExec program heapLimit depth body
        (current.setReg registers.element (current.mem (current.regs registers.pointer)))
        ((current.setReg registers.element (current.mem (current.regs registers.pointer))).setReg
          registers.accumulator
          (step (current.regs registers.accumulator) (current.mem (current.regs registers.pointer)))))
    (s : State w) (invariant : R s) (address : (s.regs registers.pointer).toNat < heapLimit) :
    SafeExec program heapLimit depth
      (Stmt.forInBody registers.pointer registers.remaining registers.element body) s
      (stepState registers
        (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s) :=
  .seq (.assign ⟨trivial, address⟩)
    (.seq (implementation s invariant) (Fold.advanceCursor_safe registers.toRegisters _ _))

/-- Verify the entire iteration construct, including both cursor assignments.
The copied cursor obeys the actual evaluation order, and the returned fold and
frame refer to the original entry state. The element local is explicitly writable. -/
theorem forIn_safe (registers : Registers) {body : Stmt} {base length : Expr} {program : Program}
    {heapLimit depth : Nat} {step : Word w → Word w → Word w} {R : State w → Prop}
    (hw : 0 < w)
    (implementation : ∀ current, R current →
      SafeExec program heapLimit depth body
        (current.setReg registers.element (current.mem (current.regs registers.pointer)))
        ((current.setReg registers.element (current.mem (current.regs registers.pointer))).setReg
          registers.accumulator
          (step (current.regs registers.accumulator) (current.mem (current.regs registers.pointer)))))
    (preserve : ∀ current, R current → R (stepState registers
      (step (current.regs registers.accumulator) (current.mem (current.regs registers.pointer)))
        current))
    (s : State w) (xs : List (Word w)) (invariant : R (initialState registers base length s))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg registers.pointer (s.eval base)).regs s.mem)
    (represented : ArrayRep s.mem (s.eval base) xs)
    (count : ((s.setReg registers.pointer (s.eval base)).eval length).toNat = xs.length)
    (heap : (s.eval base).toNat + xs.length ≤ heapLimit)
    (fit : (s.eval base).toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit depth
      (Stmt.forIn registers.pointer registers.remaining registers.element base length body) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.regs registers.pointer = arrayAddr (s.eval base) xs.length ∧
      t.regs registers.remaining = 0 ∧ R t ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r := by
  obtain ⟨t, execution, result, pointer, remaining, invariant', memory, input, output, other⟩ :=
    loop_safe_of_step registers hw
      (fun current hR address => body_safe registers implementation current hR address)
      preserve (initialState registers base length s) (s.eval base) xs invariant represented
      (initialState_pointer registers base length s)
      (by simpa only [initialState_remaining] using count) heap fit
  refine ⟨t, .seq (.assign baseReads) (.seq (.assign lengthReads) execution), ?_,
    pointer, remaining, invariant', memory, input, output, ?_⟩
  · simpa only [initialState_accumulator] using result
  · intro r hp hc ha he
    exact (other r hp hc ha he).trans (by simp [initialState, State.setReg, hp, hc])

/-- The actual element load does not change the distinct remaining local.
An inner body that preserves that local is followed by its cursor decrement. -/
theorem body_remaining (registers : Registers) {body : Stmt} {program : Program}
    {heapLimit depth : Nat}
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs registers.remaining = s.regs registers.remaining)
    {s t : State w}
    (h : SafeExec program heapLimit depth
      (Stmt.forInBody registers.pointer registers.remaining registers.element body) s t) :
    t.regs registers.remaining = s.regs registers.remaining - 1 := by
  cases h with
  | seq load rest =>
    cases load with
    | assign _ =>
      cases rest with
      | seq inner advance =>
        rw [Fold.advanceCursor_remaining registers.toRegisters advance, preserves inner]
        simp [State.setReg, Ne.symm registers.element_ne_remaining]

/-- A completed iteration contains its real element-load block, inner-body
execution and the two cursor assignments. Only the inner-body count is supplied. -/
theorem body_localMeasured (registers : Registers) {body : Stmt} {program : Program}
    {control heapLimit depth bodySteps : Nat}
    (cost : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      LocalMeasuredExec control program heapLimit depth body bodySteps s t)
    {s t : State w}
    (h : SafeExec program heapLimit depth
      (Stmt.forInBody registers.pointer registers.remaining registers.element body) s t) :
    LocalMeasuredExec control program heapLimit depth
      (Stmt.forInBody registers.pointer registers.remaining registers.element body)
      (bodySteps + 11) s t := by
  cases h with
  | seq load rest =>
    cases load with
    | assign reads =>
      cases rest with
      | seq inner advance =>
        have execution := LocalMeasuredExec.seq
          (LocalMeasuredExec.assign (control := control) reads)
          (.seq (cost inner) (Fold.advanceCursor_localMeasured registers.toRegisters advance))
        have count : LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
            (.assign registers.element (.load (.var registers.pointer))) + (bodySteps + 8) =
              bodySteps + 11 := by
          change 3 + (bodySteps + 8) = bodySteps + 11
          omega
        simpa only [count] using execution

/-- The inner body's separate exact count is combined with loads, cursor writes
and guards by the existing loop-count theorem, without a second loop induction. -/
theorem loop_localMeasured (registers : Registers) {body : Stmt} {program : Program}
    {control heapLimit depth bodySteps : Nat} (hw : 0 < w)
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs registers.remaining = s.regs registers.remaining)
    (cost : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      LocalMeasuredExec control program heapLimit depth body bodySteps s t)
    {s t : State w}
    (h : SafeExec program heapLimit depth
      (Stmt.forInLoop registers.pointer registers.remaining registers.element body) s t) :
    LocalMeasuredExec control program heapLimit depth
      (Stmt.forInLoop registers.pointer registers.remaining registers.element body)
      ((bodySteps + 14) * (s.regs registers.remaining).toNat + 2) s t :=
  Fold.loop_localMeasured_of_body registers.toRegisters hw
    (body_remaining registers preserves) (body_localMeasured registers cost) h

/-- The full iteration count includes both cursor-initialization expressions
and moves, every loaded element and the final false guard. Expression lengths
are read from generated code; `bodySteps` is justified by the inner execution. -/
theorem forIn_localMeasured (registers : Registers) {body : Stmt} {base length : Expr}
    {program : Program} {control heapLimit depth bodySteps : Nat} (hw : 0 < w)
    (preserves : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      t.regs registers.remaining = s.regs registers.remaining)
    (cost : ∀ {s t : State w}, SafeExec program heapLimit depth body s t →
      LocalMeasuredExec control program heapLimit depth body bodySteps s t)
    {s t : State w}
    (h : SafeExec program heapLimit depth
      (Stmt.forIn registers.pointer registers.remaining registers.element base length body) s t) :
    LocalMeasuredExec control program heapLimit depth
      (Stmt.forIn registers.pointer registers.remaining registers.element base length body)
      ((base.compile (ABI.scratch control)).length + (length.compile (ABI.scratch control)).length +
        (bodySteps + 14) *
          ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4) s t := by
  cases h with
  | seq first rest =>
    cases first with
    | assign baseReads =>
      cases rest with
      | seq second traversal =>
        cases second with
        | assign lengthReads =>
          have measured := loop_localMeasured registers hw preserves cost traversal
          have execution := LocalMeasuredExec.seq
            (LocalMeasuredExec.assign (control := control) baseReads)
            (.seq (LocalMeasuredExec.assign lengthReads) measured)
          have count :
              LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
                  (.assign registers.pointer base) +
                (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
                    (.assign registers.remaining length) +
                  ((bodySteps + 14) *
                    ((initialState registers base length s).regs registers.remaining).toNat + 2)) =
                (base.compile (ABI.scratch control)).length +
                  (length.compile (ABI.scratch control)).length + (bodySteps + 14) *
                    ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4 := by
            simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt, List.length_append,
              List.length_cons, List.length_nil, initialState_remaining]
            omega
          dsimp only [initialState] at count
          simpa only [count] using execution

end Ram.Source.Array.ForIn
