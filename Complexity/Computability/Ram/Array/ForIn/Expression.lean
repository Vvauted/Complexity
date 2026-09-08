/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Eval

/-!
# Array-fold functions with expression updates

These rules verify the source shape that initializes one accumulator, iterates
over an array and updates the accumulator by an actual source expression. The
array descriptor occupies the first two parameters; additional word parameters
retain their original values throughout the traversal. Generated body and return
equations determine all private locals, with no client-supplied cursor record or
loop invariant.

The expression's safety and mathematical meaning remain proof obligations.
The result is an ordinary `List.foldl`, not an executable Lean callback. The
separate measured rule counts the expression's compiled instructions, element
loads, cursor updates, guards and initialization. It does not require a proposed
time bound or change the invocation's returned value and shared state.
-/

namespace Ram.Source.Array.ForIn.Expression

private def registersOfNodup {accumulator pointer remaining element : Reg}
    (distinct : [accumulator, pointer, remaining, element].Nodup) : Registers := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  exact
    { pointer := pointer
      remaining := remaining
      accumulator := accumulator
      pointer_ne_remaining := distinct.2.1.1
      pointer_ne_accumulator := Ne.symm distinct.1.1
      remaining_ne_accumulator := Ne.symm distinct.1.2.1
      element := element
      element_ne_pointer := Ne.symm distinct.2.1.2
      element_ne_remaining := Ne.symm distinct.2.2
      element_ne_accumulator := Ne.symm distinct.1.2.2 }

private theorem parameter_ne {params accumulator pointer remaining element : Nat}
    (layout : (List.range params ++ [accumulator, pointer, remaining, element]).Nodup)
    {i : Nat} (hi : i < params) :
    i ≠ accumulator ∧ i ≠ pointer ∧ i ≠ remaining ∧ i ≠ element := by
  have separate := (List.nodup_append.mp layout).2.2
  have absent : i ∉ [accumulator, pointer, remaining, element] :=
    fun member => separate i (List.mem_range.mpr hi) i member rfl
  simpa only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
    using absent

/-- An array-first function computes a scalar fold while retaining every word
parameter. Clients prove only the actual update expression's safety and meaning;
the traversal supplies parameter preservation, termination and shared framing. -/
theorem function_contract {program : Program} {f : Func}
    {accumulator pointer remaining element seed heapLimit depth : Nat} {expression : Expr}
    {step : Word w → Word w → Word w}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1) (.assign accumulator expression)))
    (resultShape : f.result = .var accumulator)
    (array : ArrayRef w) (captures : List (Word w))
    (params : f.params = 2 + captures.length)
    (layout : (List.range f.params ++ [accumulator, pointer, remaining, element]).Nodup ∧
      f.params ≤ f.locals)
    (hw : 0 < w)
    (reads : ∀ s : State w,
      (∀ i, i < f.params → s.regs i = (array.args ++ captures)[i]?.getD 0) →
      expression.ReadsBelow heapLimit s.regs s.mem)
    (evaluate : ∀ s : State w,
      (∀ i, i < f.params → s.regs i = (array.args ++ captures)[i]?.getD 0) →
      s.eval expression = step (s.regs accumulator) (s.regs element))
    (xs : List (Word w)) (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit depth f
      (fun args entry => args = array.args ++ captures ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = xs.foldl step (BitVec.ofNat w seed) ∧ finish = entry) := by
  let registers := registersOfNodup (List.nodup_append.mp layout.1).2.1
  have fresh := @parameter_ne f.params accumulator pointer remaining element layout.1
  have hzero : 0 < f.params := by omega
  have hone : 1 < f.params := by omega
  let R := fun s : State w =>
    ∀ i, i < f.params → s.regs i = (array.args ++ captures)[i]?.getD 0
  apply FunctionContract.of_wp
  · rintro args entry ⟨rfl, _⟩
    simpa only [List.length_append, ArrayRef.length_args] using params.symm
  · exact layout.2
  · rintro args entry ⟨rfl, represented⟩
    let start := (entry.enter (array.args ++ captures)).setReg accumulator (BitVec.ofNat w seed)
    have baseValue : start.eval (.var 0) = array.base :=
      State.setReg_ne (entry.enter (array.args ++ captures)) accumulator 0
        (BitVec.ofNat w seed) (fresh hzero).1
    have lengthValue :
        (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) = array.length :=
      (State.setReg_ne start registers.pointer 1 (start.eval (.var 0))
        (fresh hone).2.1).trans
        (State.setReg_ne (entry.enter (array.args ++ captures)) accumulator 1
          (BitVec.ofNat w seed) (fresh hone).1)
    have implementation : ∀ current, R current →
        SafeExec program heapLimit depth (.assign accumulator expression)
          (current.setReg element (current.mem (current.regs pointer)))
          ((current.setReg element (current.mem (current.regs pointer))).setReg accumulator
            (step (current.regs accumulator) (current.mem (current.regs pointer)))) :=
      fun current hparams => by
        let loaded := current.setReg element (current.mem (current.regs pointer))
        have loadedParams : R loaded := fun i hi =>
          (State.setReg_ne current element i (current.mem (current.regs pointer))
            (fresh hi).2.2.2).trans (hparams i hi)
        have evaluated : loaded.eval expression =
            step (current.regs accumulator) (current.mem (current.regs pointer)) :=
          (evaluate loaded loadedParams).trans
            (congrArg₂ step
              (State.setReg_ne current element accumulator (current.mem (current.regs pointer))
                (Ne.symm registers.element_ne_accumulator))
              (State.setReg_same current element (current.mem (current.regs pointer))))
        have assigned : SafeExec program heapLimit depth (.assign accumulator expression)
            loaded (loaded.setReg accumulator (loaded.eval expression)) :=
          .assign (reads loaded loadedParams)
        simpa only [evaluated] using assigned
    have preserve : ∀ current, R current → R (stepState registers
        (step (current.regs accumulator) (current.mem (current.regs pointer))) current) :=
      fun current hparams i hi => by
        obtain ⟨ha, hp, hr, he⟩ := fresh hi
        exact (stepState_other registers _ current hp hr ha he).trans (hparams i hi)
    have initial : R (initialState registers (.var 0) (.var 1) start) := fun i hi => by
      obtain ⟨ha, hp, hr, _⟩ := fresh hi
      simp only [initialState, start, registers, registersOfNodup, State.setReg, State.enter,
        if_neg ha, if_neg hp, if_neg hr]
    obtain ⟨finish, execution, result, _, _, _, memory, input, output, _⟩ :=
      ForIn.forIn_safe registers hw implementation preserve start xs initial
        (base := .var 0) (length := .var 1) (by trivial) (by trivial)
        (by simpa only [baseValue] using represented.2.1)
        (by simpa only [lengthValue] using represented.1)
        (by simpa only [baseValue] using represented.2.2)
        (by simpa only [baseValue] using fit)
    rw [bodyShape, Verification.TotalWP.seq_iff, Verification.TotalWP.assign_iff]
    refine ⟨trivial, finish, execution, ?_, ?_, ?_⟩
    · rw [resultShape]
      trivial
    · simpa only [resultShape, State.eval, Expr.eval, start, State.setReg_same,
        registers, registersOfNodup] using result
    · change State.mk entry.regs finish.mem finish.input finish.outputRev = entry
      rw [memory, input, output]
      rfl

/-- Recover the exact compiled body count of the same completed invocation.
The expression's instruction length is counted on every iteration; no result
specification, callback price or proposed time bound supplies that count. -/
theorem function_measured {program : Program} {f : Func}
    {accumulator pointer remaining element seed control heapLimit depth : Nat} {expression : Expr}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1) (.assign accumulator expression)))
    (array : ArrayRef w) (captures : List (Word w))
    (params : f.params = 2 + captures.length)
    (layout : (List.range f.params ++ [accumulator, pointer, remaining, element]).Nodup)
    (hw : 0 < w) (xs : List (Word w)) {entry finish : State w} {value : Word w}
    (represented : array.Rep heapLimit xs entry)
    (execution : FunctionExec program heapLimit depth f (array.args ++ captures) entry value finish) :
    FunctionMeasuredExec control program heapLimit depth f (array.args ++ captures)
      (((expression.compile (ABI.scratch control)).length + 15) * xs.length + 8)
      entry value finish := by
  let registers := registersOfNodup (List.nodup_append.mp layout).2.1
  have fresh := @parameter_ne f.params accumulator pointer remaining element layout
  have hone : 1 < f.params := by omega
  obtain ⟨arity, frame, callee, body, resultReads, returned, shared⟩ := execution
  refine ⟨arity, frame, callee, ?_, resultReads, returned, shared⟩
  rw [bodyShape] at body ⊢
  cases body with
  | seq initialized rest =>
    cases initialized with
    | assign reads =>
      let start := (entry.enter (array.args ++ captures)).setReg accumulator (BitVec.ofNat w seed)
      have lengthValue :
          (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) = array.length :=
        (State.setReg_ne start registers.pointer 1 (start.eval (.var 0))
          (fresh hone).2.1).trans
          (State.setReg_ne (entry.enter (array.args ++ captures)) accumulator 1
            (BitVec.ofNat w seed) (fresh hone).1)
      have preserves : ∀ {s t : State w},
          SafeExec program heapLimit depth (.assign accumulator expression) s t →
          t.regs registers.remaining = s.regs registers.remaining := fun {s t} assigned => by
        cases assigned with
        | assign _ =>
          exact State.setReg_ne s accumulator registers.remaining _
            registers.remaining_ne_accumulator
      have cost : ∀ {s t : State w},
          SafeExec program heapLimit depth (.assign accumulator expression) s t →
          LocalMeasuredExec control program heapLimit depth (.assign accumulator expression)
            ((expression.compile (ABI.scratch control)).length + 1) s t := fun {s t} assigned => by
        cases assigned with
        | assign safe =>
          simpa only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
            List.length_append, List.length_singleton] using
            (LocalMeasuredExec.assign (control := control) (program := program)
              (d := depth) (dst := accumulator) safe)
      have loopMeasured := ForIn.forIn_localMeasured registers hw preserves cost rest
      have initialized : LocalMeasuredExec control program heapLimit depth
          (.assign accumulator (.const seed)) 2 (entry.enter (array.args ++ captures)) start :=
        .assign reads
      have full := LocalMeasuredExec.seq initialized loopMeasured
      change LocalMeasuredExec control program heapLimit depth
        (.seq (.assign accumulator (.const seed))
          (Stmt.forIn pointer remaining element (.var 0) (.var 1) (.assign accumulator expression)))
        (2 + (1 + 1 + ((expression.compile (ABI.scratch control)).length + 1 + 14) *
          ((start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1)).toNat + 4))
        (entry.enter (array.args ++ captures)) callee at full
      rw [lengthValue, represented.1] at full
      simp only [Nat.add_assoc, Nat.reduceAdd] at full
      convert full using 1; omega

/-- The function's body-time observation records that same exact count. -/
theorem function_bodyTime {program : Program} {f : Func}
    {accumulator pointer remaining element seed control heapLimit depth : Nat} {expression : Expr}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1) (.assign accumulator expression)))
    (array : ArrayRef w) (captures : List (Word w))
    (params : f.params = 2 + captures.length)
    (layout : (List.range f.params ++ [accumulator, pointer, remaining, element]).Nodup)
    (hw : 0 < w) (xs : List (Word w)) {entry finish : State w} {value : Word w}
    (represented : array.Rep heapLimit xs entry)
    (execution : FunctionExec program heapLimit depth f (array.args ++ captures) entry value finish) :
    f.bodyTime program heapLimit (array.args ++ captures) entry = Part.some
      (((expression.compile (ABI.scratch control)).length + 15) * xs.length + 8) :=
  (function_measured bodyShape array captures params layout hw xs represented execution).bodyTime_eq_some

end Ram.Source.Array.ForIn.Expression
