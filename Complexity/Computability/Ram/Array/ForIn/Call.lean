/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn
import Complexity.Computability.Ram.Array.Fold.Call
import Complexity.Computability.Ram.Array.Model
import Complexity.Data.List.Fold
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Computability.Ram.Verification.Time.ForIn
import Complexity.Computability.Ram.Verification.Time.Function

/-!
# Array iteration with a verified scalar function call

Each iteration loads an array element and passes that word and the accumulator
to a fixed source function. Its budget-free contract establishes the mathematical
step and preservation of shared state. The array-iteration rule supplies cursor
progress, termination and framing; no Lean callback is executed for free.

The separate exact-count theorem accepts a proved constant callee-body count.
The existing call compiler adds argument evaluation, frame handling and return
instructions, while the iteration rule counts initialization, loads and guards.

The uniform conditional time-bound rules instead accept a helper's function-level
upper bound without assuming helper totality. The prefix-dependent rules sum
that independent bound at each actual accumulator and element; a separate
read-only contract identifies these arguments and preserves the unread suffix.
Only admitted inputs require that contract, never the empty endpoint or unrelated
words. Neither form requires exact counts for arbitrary body-entry states.
-/

namespace Ram.Source.Array.ForIn.Call

/-- The actual two-argument call after the iteration has loaded its element. -/
def body (registers : Registers) (fn : Nat) : Stmt :=
  .call [registers.accumulator] fn [.var registers.accumulator, .var registers.element]

/-- Apply a helper contract only to the two actual argument words at this call
site. No behavior on other accumulator/element pairs is assumed. -/
theorem body_safe_at (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {step : Word w → Word w → Word w}
    (lookup : program[fn]? = some f) (s : State w)
    (contract : FunctionContract program heapLimit depth f
      (fun args _ => args = [s.regs registers.accumulator, s.regs registers.element])
      (fun _ entry value finish => value =
        [step (s.regs registers.accumulator) (s.regs registers.element)] ∧ finish = entry)) :
    SafeExec program heapLimit (depth + 1) (body registers fn) s
      (s.setReg registers.accumulator
        (step (s.regs registers.accumulator) (s.regs registers.element))) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    contract [s.regs registers.accumulator, s.regs registers.element] s rfl
  have resultCount : [registers.accumulator].length = f.results.length := by
    simpa only [List.length_cons, List.length_nil] using execution.length_eq
  exact execution.call (dsts := [registers.accumulator])
    (exprs := [.var registers.accumulator, .var registers.element]) lookup resultCount
    (by simp [Expr.ReadsBelow])

/-- A verified source function implements one accumulator update on the loaded
word. Its returned value is assigned by the actual call instruction. -/
theorem body_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {step : Word w → Word w → Word w}
    (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (s : State w) :
    SafeExec program heapLimit (depth + 1) (body registers fn) s
      (s.setReg registers.accumulator
        (step (s.regs registers.accumulator) (s.regs registers.element))) :=
  body_safe_at registers lookup s
    (contract (s.regs registers.accumulator) (s.regs registers.element))

/-- Read a represented array through one fixed, verified function call per
element. The input expressions are evaluated in source order, and the frame
excludes the accumulator, element binding and both private cursor locals. -/
theorem forIn_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {base length : Expr} {step : Word w → Word w → Word w}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (s : State w) (xs : List (Word w))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg registers.pointer (s.eval base)).regs s.mem)
    (represented : ArrayRep s.mem (s.eval base) xs)
    (count : ((s.setReg registers.pointer (s.eval base)).eval length).toNat = xs.length)
    (heap : (s.eval base).toNat + xs.length ≤ heapLimit)
    (fit : (s.eval base).toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit (depth + 1)
        (Stmt.forIn registers.pointer registers.remaining registers.element base length
          (body registers fn)) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r := by
  obtain ⟨t, execution, result, _, _, _, memory, input, output, other⟩ :=
    ForIn.forIn_safe registers (R := fun _ => True) hw
      (fun current _ => by
        simpa only [State.setReg, if_neg (Ne.symm registers.element_ne_accumulator),
          if_pos rfl] using
          body_safe registers lookup contract
            (current.setReg registers.element (current.mem (current.regs registers.pointer))))
      (by intros; trivial) s xs trivial baseReads lengthReads represented count heap fit
  exact ⟨t, execution, result, memory, input, output, other⟩

/-- The call restores its caller locals before assigning the accumulator, so
the private remaining-count local is unchanged even without a functional spec. -/
theorem body_remaining (registers : Registers) {program : Program}
    {fn heapLimit depth : Nat} {s t : State w}
    (h : SafeExec program heapLimit depth (body registers fn) s t) :
    t.regs registers.remaining = s.regs registers.remaining := by
  cases h with
  | call _ _ _ _ _ _ _ =>
    simp [State.leave, registers.remaining_ne_accumulator]

/-- A proved constant callee-body count determines this call's exact cost,
including both scalar arguments, the callee-sized frame and its return code. -/
theorem body_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat}
    (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1) (body registers fn) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1) (body registers fn)
      (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
        bodySteps) s t := by
  obtain ⟨steps, measured⟩ := h.exists_localMeasured control
  cases measured with
  | call found arity resultCount frame arguments callee results =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have count := cost callee
    have call := LocalMeasuredExec.call (dsts := [registers.accumulator])
      found arity resultCount frame arguments callee results
    rw [count] at call
    exact call

/-- Count the same completed iteration, including cursor initialization, every
element load, both cursor updates and the loop's guards and backedges. The cost
premise concerns the actual callee body, independently of functional correctness. -/
theorem forIn_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat} {base length : Expr}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn)) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn))
      ((base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
          bodySteps + 14) *
          ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4) s t :=
  ForIn.forIn_localMeasured registers hw (body_remaining registers)
    (body_localMeasured registers lookup cost) h

/-- Apply the helper's conditional bound to the actual two-argument call. -/
private theorem body_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat}
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1) (body registers fn) (fun _ => True)
      (fun _ => Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget) := by
  simpa only [body, Fold.Call.callSteps, List.length_cons, List.length_nil] using
    time.call (dsts := [registers.accumulator])
      (args := [.var registers.accumulator, .var registers.element])
      (R := fun _ => True) lookup (fun _ _ => by simp)

/-- Bound every completed iteration loop without assuming that its helper
terminates on other inputs. The existing linear-loop rule is applied only to
states with a completed suffix, witnessed by the very execution being bounded. -/
theorem loop_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat} (hw : 0 < w)
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1)
      (Stmt.forInLoop registers.pointer registers.remaining registers.element (body registers fn))
      (fun _ => True)
      (fun s => (Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget + 14) *
          (s.regs registers.remaining).toNat + 2) :=
  TimeBound.forInLoop registers.pointer registers.remaining registers.element hw
    registers.pointer_ne_remaining registers.element_ne_remaining
    (body_remaining registers) (body_timeBound registers lookup time)

/-- The conditional bound for the complete iteration construct includes both
descriptor copies, all actual calls and loads, cursor writes and the final guard. -/
theorem forIn_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat} {base length : Expr} (hw : 0 < w)
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn)) (fun _ => True)
      (fun s => (base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
          bodyBudget + 14) *
          ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4) :=
  TimeBound.forIn registers.pointer registers.remaining registers.element hw
    registers.pointer_ne_remaining registers.element_ne_remaining
    (body_remaining registers) (body_timeBound registers lookup time)

/-! ## Bounds depending on the actual fold prefixes -/

private def remainingWords (registers : Registers) (s : State w) : List (Word w) :=
  arrayContents s.mem (s.regs registers.pointer) (s.regs registers.remaining).toNat

private theorem remainingWords_eq (registers : Registers) {heapLimit : Nat}
    {target : Word w} {xs : List (Word w)} {s : State w}
    (cursor : Fold.Cursor registers.toRegisters heapLimit target xs s) :
    remainingWords registers s = xs := by
  unfold remainingWords
  rw [cursor.count]
  exact cursor.array.contents_eq

private structure StepInvariant (registers : Registers) (heapLimit : Nat)
    (target : Word w) (I Allowed : Word w → Prop) (s : State w) : Prop where
  cursor : Fold.Cursor registers.toRegisters heapLimit target (remainingWords registers s) s
  accumulator : I (s.regs registers.accumulator)
  elements : ∀ x ∈ remainingWords registers s, Allowed x

private theorem StepInvariant.cons (registers : Registers) {heapLimit : Nat}
    {target : Word w} {I Allowed : Word w → Prop} {s : State w}
    (invariant : StepInvariant registers heapLimit target I Allowed s)
    (nonzero : s.regs registers.remaining ≠ 0) :
    ∃ x xs, remainingWords registers s = x :: xs := by
  cases words : remainingWords registers s with
  | nil =>
    have zero := invariant.cursor.count
    rw [words] at zero
    exact False.elim (nonzero ((Word.toNat_eq_zero_iff _).mp zero))
  | cons x xs => exact ⟨x, xs, rfl⟩

private theorem StepInvariant.head (registers : Registers) {heapLimit : Nat}
    {target : Word w} {I Allowed : Word w → Prop} {s : State w}
    (invariant : StepInvariant registers heapLimit target I Allowed s)
    (nonzero : s.regs registers.remaining ≠ 0) :
    Allowed (s.mem (s.regs registers.pointer)) ∧
      (s.regs registers.pointer).toNat < heapLimit := by
  obtain ⟨x, xs, words⟩ := invariant.cons registers nonzero
  have cursor : Fold.Cursor registers.toRegisters heapLimit target (x :: xs) s :=
    words ▸ invariant.cursor
  rw [cursor.head]
  exact ⟨invariant.elements x (by rw [words]; exact List.mem_cons_self), cursor.address_lt⟩

private theorem StepInvariant.advance (registers : Registers) {heapLimit : Nat}
    {target : Word w} {I Allowed : Word w → Prop} {step : Word w → Word w → Word w}
    (hw : 0 < w)
    (preserve : ∀ a x, I a → Allowed x → I (step a x)) {s : State w}
    (invariant : StepInvariant registers heapLimit target I Allowed s)
    (nonzero : s.regs registers.remaining ≠ 0) :
    StepInvariant registers heapLimit target I Allowed
      (stepState registers
        (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s) := by
  obtain ⟨x, xs, words⟩ := invariant.cons registers nonzero
  have cursor : Fold.Cursor registers.toRegisters heapLimit target (x :: xs) s :=
    words ▸ invariant.cursor
  let value := step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))
  have next := cursor.advance hw (stepState_mem registers value s)
    (stepState_pointer registers value s) (stepState_remaining registers value s)
  have nextWords := remainingWords_eq registers next
  refine ⟨nextWords.symm ▸ next, ?_, ?_⟩
  · rw [stepState_accumulator, cursor.head]
    exact preserve _ _ invariant.accumulator
      (invariant.elements x (by rw [words]; exact List.mem_cons_self))
  · intro y hy
    exact invariant.elements y (by rw [words]; exact List.mem_cons_of_mem x (nextWords ▸ hy))

private theorem iteration_safe_of_step (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {step : Word w → Word w → Word w}
    {I Allowed : Word w → Prop} (lookup : program[fn]? = some f)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth f
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (s : State w) (accumulator : I (s.regs registers.accumulator))
    (element : Allowed (s.mem (s.regs registers.pointer)))
    (address : (s.regs registers.pointer).toNat < heapLimit) :
    SafeExec program heapLimit (depth + 1)
      (Stmt.forInBody registers.pointer registers.remaining registers.element (body registers fn)) s
      (stepState registers
        (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s) := by
  apply ForIn.body_safe registers (R := fun current =>
    I (current.regs registers.accumulator) ∧ Allowed (current.mem (current.regs registers.pointer)))
    (s := s) (invariant := ⟨accumulator, element⟩) (address := address)
  intro current admissible
  let loaded := current.setReg registers.element (current.mem (current.regs registers.pointer))
  have contract := correct (current.regs registers.accumulator)
    (current.mem (current.regs registers.pointer)) admissible.1 admissible.2
  have call := body_safe_at registers lookup loaded (by
    simpa only [loaded, State.setReg, if_neg (Ne.symm registers.element_ne_accumulator),
      if_pos rfl] using contract)
  simpa only [loaded, State.setReg, if_neg (Ne.symm registers.element_ne_accumulator),
    if_pos rfl] using call

/-- A read-only fold may restrict helper correctness to an invariant on the
accumulator and an admitted domain of actual array elements. Nothing is required
of the helper at the empty endpoint or on unrelated words. -/
theorem forIn_safe_of_step (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {base length : Expr} {step : Word w → Word w → Word w}
    {I Allowed : Word w → Prop} (hw : 0 < w) (lookup : program[fn]? = some f)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth f
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (preserve : ∀ a x, I a → Allowed x → I (step a x))
    (s : State w) (xs : List (Word w)) (initial : I (s.regs registers.accumulator))
    (admissible : ∀ x ∈ xs, Allowed x)
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg registers.pointer (s.eval base)).regs s.mem)
    (represented : ArrayRep s.mem (s.eval base) xs)
    (count : ((s.setReg registers.pointer (s.eval base)).eval length).toNat = xs.length)
    (heap : (s.eval base).toNat + xs.length ≤ heapLimit)
    (fit : (s.eval base).toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit (depth + 1)
        (Stmt.forIn registers.pointer registers.remaining registers.element base length
          (body registers fn)) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r := by
  let target := arrayAddr (s.eval base) xs.length
  let start := initialState registers base length s
  have cursor : Fold.Cursor registers.toRegisters heapLimit target xs start := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [start, initialState_pointer] using represented
    · simpa only [start, initialState_pointer] using heap
    · simpa only [start, initialState_remaining] using count
    · simpa only [start, initialState_pointer] using fit
    · simp only [start, initialState_pointer, target]
  have startWords := remainingWords_eq registers cursor
  have invariant : StepInvariant registers heapLimit target I Allowed start :=
    ⟨startWords.symm ▸ cursor, by simpa only [start, initialState_accumulator] using initial,
      fun x hx => admissible x (startWords ▸ hx)⟩
  obtain ⟨t, execution, result, _, _, _, memory, input, output, other⟩ :=
    ForIn.loop_safe_of_step_guarded registers
      (R := StepInvariant registers heapLimit target I Allowed) hw
      (fun current h nonzero _ => iteration_safe_of_step registers lookup correct current
        h.accumulator (h.head registers nonzero).1 (h.head registers nonzero).2)
      (fun current h nonzero => h.advance registers hw preserve nonzero)
      start (s.eval base) xs invariant represented
      (initialState_pointer registers base length s)
      (by simpa only [start, initialState_remaining] using count) heap fit
  refine ⟨t, .seq (.assign baseReads) (.seq (.assign lengthReads) execution), ?_,
    memory, input, output, ?_⟩
  · simpa only [start, initialState_accumulator] using result
  · intro r hp hr ha he
    exact (other r hp hr ha he).trans (by simp [start, initialState, State.setReg, hp, hr])

private theorem iteration_timeBound_of_step (registers : Registers)
    {program : Program} {f : Func} {w control fn heapLimit depth : Nat}
    {C : Word w → Word w → Nat} {I Allowed : Word w → Prop}
    (lookup : program[fn]? = some f)
    (time : ∀ a x, I a → Allowed x → FunctionTimeBound control program heapLimit depth f
      (fun args _ => args = [a, x]) (fun _ _ => C a x)) :
    TimeBound control program heapLimit (depth + 1)
      (Stmt.forInBody registers.pointer registers.remaining registers.element (body registers fn))
      (fun s => I (s.regs registers.accumulator) ∧ Allowed (s.mem (s.regs registers.pointer)))
      (fun s => C (s.regs registers.accumulator) (s.mem (s.regs registers.pointer)) +
        Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element] 0 +
          11) := by
  intro s admissible steps t execution
  cases execution with
  | seq loaded rest =>
    cases loaded with
    | assign _ =>
      cases rest with
      | seq called advance =>
        let entry := s.setReg registers.element (s.mem (s.regs registers.pointer))
        have callBound : TimeBound control program heapLimit (depth + 1) (body registers fn)
            (fun current => current = entry)
            (fun _ => Fold.Call.callSteps control f
              [.var registers.accumulator, .var registers.element]
              (C (s.regs registers.accumulator) (s.mem (s.regs registers.pointer)))) := by
          apply (time _ _ admissible.1 admissible.2).call_at lookup
          · simp only [entry, List.map_cons, List.map_nil, State.eval, Expr.eval,
              State.setReg, if_neg (Ne.symm registers.element_ne_accumulator), ite_true]
          · exact Nat.le_refl _
        have callCount := callBound entry rfl _ _ called
        have advanceCount := (advance.deterministic
          (Fold.advanceCursor_localMeasured registers.toRegisters advance.erase)).1
        change 3 + (_ + _) ≤ C (s.regs registers.accumulator)
          (s.mem (s.regs registers.pointer)) +
            Fold.Call.callSteps control f
              [.var registers.accumulator, .var registers.element] 0 + 11
        dsimp only [Fold.Call.callSteps] at callCount ⊢
        omega

private theorem loop_timeBound_of_step (registers : Registers)
    {program : Program} {f : Func} {w control fn heapLimit depth : Nat}
    {step : Word w → Word w → Word w} {C : Word w → Word w → Nat}
    {I Allowed : Word w → Prop} (hw : 0 < w) (lookup : program[fn]? = some f)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth f
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (time : ∀ a x, I a → Allowed x → FunctionTimeBound control program heapLimit depth f
      (fun args _ => args = [a, x]) (fun _ _ => C a x))
    (preserve : ∀ a x, I a → Allowed x → I (step a x)) (target : Word w) :
    TimeBound control program heapLimit (depth + 1)
      (Stmt.forInLoop registers.pointer registers.remaining registers.element (body registers fn))
      (StepInvariant registers heapLimit target I Allowed)
      (fun s => ((remainingWords registers s).mapIdx (fun i x =>
          C (((remainingWords registers s).take i).foldl step (s.regs registers.accumulator))
            x)).sum +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element] 0 +
          14) * (remainingWords registers s).length + 2) := by
  let invariant := StepInvariant registers heapLimit target I Allowed
  let potential := fun s : State w =>
    ((remainingWords registers s).mapIdx (fun i x =>
      C (((remainingWords registers s).take i).foldl step (s.regs registers.accumulator)) x)).sum +
      (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element] 0 +
        14) * (remainingWords registers s).length + 2
  let iterationBound := fun s : State w =>
    C (s.regs registers.accumulator) (s.mem (s.regs registers.pointer)) +
      Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element] 0 + 11
  apply TimeBound.while_potential invariant potential iterationBound
    (R := fun s t => t = stepState registers
      (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s)
  · rintro s ⟨admissible, nonzero⟩
    exact ⟨_, iteration_safe_of_step registers lookup correct s admissible.accumulator
      (admissible.head registers nonzero).1 (admissible.head registers nonzero).2, rfl⟩
  · exact (iteration_timeBound_of_step registers lookup time).consequence
      (fun s h => ⟨h.1.accumulator, (h.1.head registers h.2).1⟩)
      (fun _ _ => Nat.le_refl _)
  · intro s _ _
    change 1 + 1 ≤ potential s
    dsimp only [potential]
    omega
  · rintro s t admissible nonzero rfl
    refine ⟨admissible.advance registers hw preserve nonzero, ?_⟩
    obtain ⟨x, xs, words⟩ := admissible.cons registers nonzero
    have cursor : Fold.Cursor registers.toRegisters heapLimit target (x :: xs) s :=
      words ▸ admissible.cursor
    let value := step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))
    have next := cursor.advance hw (stepState_mem registers value s)
      (stepState_pointer registers value s) (stepState_remaining registers value s)
    have nextWords := remainingWords_eq registers next
    dsimp only [value] at nextWords
    rw [cursor.head] at nextWords
    change 1 + 1 + iterationBound s + 1 + potential _ ≤ potential s
    simp only [potential, iterationBound, words, nextWords, stepState_accumulator, cursor.head,
      List.sum_mapIdx_foldl_take_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Bound a completed read-only traversal by the helper cost on each actual
element and preceding fold accumulator. The separate helper contract is needed
only on admitted inputs to identify those values and preserve the unread memory.
The expression `mapIdx`/`take` is a mathematical sum, not executable work supplied
to the RAM program. All actual calls, loads, cursor writes and guards are charged. -/
theorem forIn_timeBound_of_step (registers : Registers)
    {program : Program} {f : Func} {w control fn heapLimit depth : Nat} {base length : Expr}
    {step : Word w → Word w → Word w} {C : Word w → Word w → Nat}
    {I Allowed : Word w → Prop} (hw : 0 < w) (lookup : program[fn]? = some f)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth f
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (time : ∀ a x, I a → Allowed x → FunctionTimeBound control program heapLimit depth f
      (fun args _ => args = [a, x]) (fun _ _ => C a x))
    (preserve : ∀ a x, I a → Allowed x → I (step a x))
    (xs : List (Word w)) (admissible : ∀ x ∈ xs, Allowed x) :
    TimeBound control program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn))
      (fun s => ArrayRep s.mem (s.eval base) xs ∧
        ((s.setReg registers.pointer (s.eval base)).eval length).toNat = xs.length ∧
        (s.eval base).toNat + xs.length ≤ heapLimit ∧
        (s.eval base).toNat + xs.length < 2 ^ w ∧ I (s.regs registers.accumulator))
      (fun s => (base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (xs.mapIdx (fun i x => C ((xs.take i).foldl step (s.regs registers.accumulator)) x)).sum +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element] 0 +
          14) * xs.length + 4) := by
  rintro s ⟨represented, count, heap, fit, initial⟩ steps finish execution
  let target := arrayAddr (s.eval base) xs.length
  let start := initialState registers base length s
  have cursor : Fold.Cursor registers.toRegisters heapLimit target xs start := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [start, initialState_pointer] using represented
    · simpa only [start, initialState_pointer] using heap
    · simpa only [start, initialState_remaining] using count
    · simpa only [start, initialState_pointer] using fit
    · simp only [start, initialState_pointer, target]
  have startWords := remainingWords_eq registers cursor
  have invariant : StepInvariant registers heapLimit target I Allowed start :=
    ⟨startWords.symm ▸ cursor, by simpa only [start, initialState_accumulator] using initial,
      fun x hx => admissible x (startWords ▸ hx)⟩
  cases execution with
  | seq first rest =>
    cases first with
    | assign _ =>
      cases rest with
      | seq second traversal =>
        cases second with
        | assign _ =>
          have bounded := loop_timeBound_of_step registers hw lookup correct time preserve target
            start invariant _ finish traversal
          dsimp only at bounded ⊢
          rw [startWords] at bounded
          simp only [start, initialState_accumulator] at bounded
          simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
            List.length_append, List.length_singleton]
          omega

end Ram.Source.Array.ForIn.Call
