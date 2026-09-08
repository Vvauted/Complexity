/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn.Call
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Verification.Function

/-!
# Function contracts for array iteration through verified calls

`Ram.Source.Array.ForIn.function_contract` handles a common single-array
function: initialize one scalar accumulator, iterate over the array, call a
verified scalar update for each element, and return the accumulator. The body
and return equations determine its local slots and call target. Clients provide
the mathematical update contract and array premises, not a cursor or register
record. The one returned field is an ordinary `List.foldl`, with the caller state
unchanged.

`Ram.Source.Array.ForIn.function_bodyTime` separately observes the body count
of a completed invocation, using a theorem about the helper's actual compiled
body. Its count includes iteration and initialization, but not the enclosing
call to the array function itself.

`Ram.Source.Array.ForIn.function_timeBound` instead accepts a uniform conditional
bound on helper invocations with two arguments. It does not require an exact
helper-body count or assume that helper calls on other states terminate.

`function_contract_of_step` restricts correctness to admitted array elements and
an accumulator invariant. `function_timeBound_of_step` independently sums the
helper's conditional bound at each element and preceding fold accumulator. Its
read-only correctness premise identifies those actual arguments; it is not a
time requirement on the mathematical contract.

The rule applies to the displayed source shape, not arbitrary array programs.
Its freshness premise separates parameters, accumulator and iteration locals.
Array contents are already represented in memory; neither the mathematical list
nor its fold is an executable primitive or an implicit loader.
-/

namespace Ram.Source.Array.ForIn

private def registersOfNodup {accumulator pointer remaining element : Reg}
    (distinct : [0, 1, accumulator, pointer, remaining, element].Nodup) : Registers := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  exact
    { pointer := pointer
      remaining := remaining
      accumulator := accumulator
      pointer_ne_remaining := distinct.2.2.2.1.1
      pointer_ne_accumulator := Ne.symm distinct.2.2.1.1
      remaining_ne_accumulator := Ne.symm distinct.2.2.1.2.1
      element := element
      element_ne_pointer := Ne.symm distinct.2.2.2.1.2
      element_ne_remaining := Ne.symm distinct.2.2.2.2
      element_ne_accumulator := Ne.symm distinct.2.2.1.2.2 }

/-- A single-array function computes a read-only fold using helper contracts
only on admitted elements and accumulator values. The helper need not terminate
on unrelated words or at an empty array's unexecuted endpoint. This correctness
rule has no cost premise. -/
theorem function_contract_of_step {program : Program} {f helper : Func}
    {accumulator pointer remaining element fn seed heapLimit depth : Nat}
    {step : Word w → Word w → Word w} {I Allowed : Word w → Prop}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call [accumulator] fn [.var accumulator, .var element])))
    (resultShape : f.results = [.var accumulator]) (params : f.params = 2)
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup ∧ 2 ≤ f.locals)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth helper
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (preserve : ∀ a x, I a → Allowed x → I (step a x))
    (array : ArrayRef w) (xs : List (Word w))
    (initial : I (BitVec.ofNat w seed)) (admissible : ∀ x ∈ xs, Allowed x)
    (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit (depth + 1) f
      (fun args entry => args = array.args ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = [xs.foldl step (BitVec.ofNat w seed)] ∧ finish = entry) := by
  let registers := registersOfNodup layout.1
  have distinct := layout.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  have ha0 : accumulator ≠ 0 := by omega
  have ha1 : accumulator ≠ 1 := by omega
  have hp1 : pointer ≠ 1 := by omega
  apply FunctionContract.of_wp
  · rintro args entry ⟨rfl, _⟩
    simpa only [ArrayRef.length_args] using params.symm
  · omega
  · rintro args entry ⟨rfl, represented⟩
    let start := (entry.enter array.args).setReg accumulator (BitVec.ofNat w seed)
    have baseValue : start.eval (.var 0) = array.base :=
      State.setReg_ne (entry.enter array.args) accumulator 0 (BitVec.ofNat w seed) (Ne.symm ha0)
    have lengthValue :
        (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) =
          array.length :=
      (State.setReg_ne start registers.pointer 1 (start.eval (.var 0)) (Ne.symm hp1)).trans
        (State.setReg_ne (entry.enter array.args) accumulator 1 (BitVec.ofNat w seed) (Ne.symm ha1))
    obtain ⟨finish, execution, result, memory, input, output, _⟩ :=
      Call.forIn_safe_of_step registers hw lookup correct preserve start xs
        (base := .var 0) (length := .var 1)
        (by simpa only [start, State.setReg_same, registers, registersOfNodup] using initial)
        admissible (by trivial) (by trivial)
        (by simpa only [baseValue] using represented.2.1)
        (by simpa only [lengthValue] using represented.1)
        (by simpa only [baseValue] using represented.2.2)
        (by simpa only [baseValue] using fit)
    rw [bodyShape, Verification.TotalWP.seq_iff, Verification.TotalWP.assign_iff]
    refine ⟨trivial, finish, ?_, ?_⟩
    · simpa only [Call.body, registers, registersOfNodup] using execution
    · refine ⟨?_, ?_, ?_⟩
      · simp [resultShape, Expr.ReadsBelow]
      · simpa only [resultShape, List.map_cons, List.map_nil, State.eval, Expr.eval,
          start, State.setReg_same, registers, registersOfNodup] using
          congrArg (fun value => [value]) result
      · change State.mk entry.regs finish.mem finish.input finish.outputRev = entry
        rw [memory, input, output]
        rfl

/-- A single-array function computes a read-only scalar fold through actual
calls. Generated body/result equations infer every local slot; the layout
premise is a decidable fact about those slots. The helper's contract, not a
host callback, supplies each mathematical accumulator update. -/
theorem function_contract {program : Program} {f helper : Func}
    {accumulator pointer remaining element fn seed heapLimit depth : Nat}
    {step : Word w → Word w → Word w}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call [accumulator] fn [.var accumulator, .var element])))
    (resultShape : f.results = [.var accumulator]) (params : f.params = 2)
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup ∧ 2 ≤ f.locals)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (contract : ∀ a x, FunctionContract program heapLimit depth helper
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (array : ArrayRef w) (xs : List (Word w))
    (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit (depth + 1) f
      (fun args entry => args = array.args ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = [xs.foldl step (BitVec.ofNat w seed)] ∧ finish = entry) :=
  function_contract_of_step (I := fun _ => True) (Allowed := fun _ => True)
    bodyShape resultShape params layout hw lookup (fun a x _ _ => contract a x)
    (by intros; trivial) array xs trivial (by intros; trivial) fit

/-- The same completed function invocation has the count obtained from the
helper's measured body and its actual call instructions. The surrounding
iteration includes its loads, cursor updates, guards and initialization; the
function also executes the initial accumulator assignment. -/
theorem function_bodyTime {program : Program} {f helper : Func}
    {accumulator pointer remaining element fn seed control heapLimit depth bodySteps : Nat}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call [accumulator] fn [.var accumulator, .var element])))
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth helper.body steps s t → steps = bodySteps)
    (array : ArrayRef w) (xs : List (Word w)) {entry finish : State w} {value : List (Word w)}
    (represented : array.Rep heapLimit xs entry)
    (execution : FunctionExec program heapLimit (depth + 1) f array.args entry value finish) :
    f.bodyTime program heapLimit array.args entry = Part.some
      ((Fold.Call.callSteps control helper [.var accumulator, .var element] bodySteps + 14) *
        xs.length + 8) := by
  let registers := registersOfNodup layout
  have distinct := layout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  have ha1 : accumulator ≠ 1 := by omega
  have hp1 : pointer ≠ 1 := by omega
  obtain ⟨arity, frame, callee, body, resultReads, _, _⟩ := execution
  have measured : LocalMeasuredExec control program heapLimit (depth + 1) f.body
      ((Fold.Call.callSteps control helper [.var accumulator, .var element] bodySteps + 14) *
        xs.length + 8) (entry.enter array.args) callee := by
    rw [bodyShape] at body ⊢
    cases body with
    | seq initialized rest =>
      cases initialized with
      | assign reads =>
        let start := (entry.enter array.args).setReg accumulator (BitVec.ofNat w seed)
        have lengthValue :
            (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) =
              array.length :=
          (State.setReg_ne start registers.pointer 1 (start.eval (.var 0)) (Ne.symm hp1)).trans
            (State.setReg_ne (entry.enter array.args) accumulator 1
              (BitVec.ofNat w seed) (Ne.symm ha1))
        have loopMeasured := Call.forIn_localMeasured registers hw lookup cost
          (s := start) (base := .var 0) (length := .var 1)
          (by simpa only [Call.body, registers, registersOfNodup] using rest)
        have initialized : LocalMeasuredExec control program heapLimit (depth + 1)
            (.assign accumulator (.const seed)) 2 (entry.enter array.args) start :=
          .assign reads
        have full := LocalMeasuredExec.seq initialized loopMeasured
        change LocalMeasuredExec control program heapLimit (depth + 1)
          (.seq (.assign accumulator (.const seed))
            (Stmt.forIn pointer remaining element (.var 0) (.var 1)
              (.call [accumulator] fn [.var accumulator, .var element])))
          (2 + (1 + 1 +
            (Fold.Call.callSteps control helper [.var accumulator, .var element] bodySteps + 14) *
              ((start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1)).toNat + 4))
          (entry.enter array.args) callee at full
        rw [lengthValue, represented.1] at full
        convert full using 1; omega
  exact (FunctionMeasuredExec.of_body arity frame measured resultReads).bodyTime_eq_some

/-- A uniform bound on actual helper invocations gives a separate bound for the
array function's body. The generated body determines its private locals and
call arguments. Completed execution supplies call safety and progress; no helper
totality, mathematical fold specification or exact helper count is assumed.
The outer function's own return expressions and enclosing call are not body work. -/
theorem function_timeBound {program : Program} {f helper : Func}
    {w accumulator pointer remaining element fn seed control heapLimit depth bodyBudget : Nat}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call [accumulator] fn [.var accumulator, .var element])))
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (time : FunctionTimeBound (w := w) control program heapLimit depth helper
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget))
    (array : ArrayRef w) (xs : List (Word w)) :
    FunctionTimeBound (w := w) control program heapLimit (depth + 1) f
      (fun args entry => args = array.args ∧ array.Rep heapLimit xs entry)
      (fun _ _ => (Fold.Call.callSteps control helper
        [.var accumulator, .var element] bodyBudget + 14) * xs.length + 8) := by
  let registers := registersOfNodup layout
  have distinct := layout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  have ha1 : accumulator ≠ 1 := by omega
  have hp1 : pointer ≠ 1 := by omega
  rintro args entry ⟨rfl, represented⟩ steps value finish invocation
  obtain ⟨_, _, callee, execution, _, _, _⟩ := invocation
  rw [bodyShape] at execution
  cases execution with
  | seq initialized traversal =>
    cases initialized with
    | assign _ =>
      let start := (entry.enter array.args).setReg accumulator (BitVec.ofNat w seed)
      have lengthValue :
          (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) =
            array.length :=
        (State.setReg_ne start registers.pointer 1 (start.eval (.var 0)) (Ne.symm hp1)).trans
          (State.setReg_ne (entry.enter array.args) accumulator 1
            (BitVec.ofNat w seed) (Ne.symm ha1))
      have bounded := Call.forIn_timeBound registers hw lookup time
        (base := .var 0) (length := .var 1) start trivial _ callee
        (by simpa only [Call.body, registers, registersOfNodup] using traversal)
      dsimp only at bounded
      rw [lengthValue, represented.1] at bounded
      change _ ≤ 1 + 1 + (Fold.Call.callSteps control helper
        [.var accumulator, .var element] bodyBudget + 14) * xs.length + 4 at bounded
      change 2 + _ ≤ (Fold.Call.callSteps control helper
        [.var accumulator, .var element] bodyBudget + 14) * xs.length + 8
      omega

/-- The helper's separate conditional body bound is summed at each real
element and its preceding mathematical fold accumulator. Its independent
read-only contract identifies these arguments and preserves the unread array;
no body-count or cost assumption enters that correctness contract.

This counts the array function's body, including initialization and the real
helper-call ABI. Its own return expressions and enclosing call remain outside
the body bound. The uniform rule above does not need these functional premises. -/
theorem function_timeBound_of_step {program : Program} {f helper : Func}
    {w accumulator pointer remaining element fn seed control heapLimit depth : Nat}
    {step : Word w → Word w → Word w} {C : Word w → Word w → Nat}
    {I Allowed : Word w → Prop}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call [accumulator] fn [.var accumulator, .var element])))
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (correct : ∀ a x, I a → Allowed x → FunctionContract program heapLimit depth helper
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = [step a x] ∧ finish = entry))
    (time : ∀ a x, I a → Allowed x → FunctionTimeBound control program heapLimit depth helper
      (fun args _ => args = [a, x]) (fun _ _ => C a x))
    (preserve : ∀ a x, I a → Allowed x → I (step a x))
    (array : ArrayRef w) (xs : List (Word w))
    (initial : I (BitVec.ofNat w seed)) (admissible : ∀ x ∈ xs, Allowed x)
    (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit (depth + 1) f
      (fun args entry => args = array.args ∧ array.Rep heapLimit xs entry)
      (fun _ _ =>
        (xs.mapIdx (fun i x => C ((xs.take i).foldl step (BitVec.ofNat w seed)) x)).sum +
        (Fold.Call.callSteps control helper [.var accumulator, .var element] 0 + 14) *
          xs.length + 8) := by
  let registers := registersOfNodup layout
  have distinct := layout
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  have ha0 : accumulator ≠ 0 := by omega
  have ha1 : accumulator ≠ 1 := by omega
  have hp1 : pointer ≠ 1 := by omega
  rintro args entry ⟨rfl, represented⟩ steps value finish invocation
  obtain ⟨_, _, callee, execution, _, _, _⟩ := invocation
  rw [bodyShape] at execution
  cases execution with
  | seq initialized traversal =>
    cases initialized with
    | assign _ =>
      let start := (entry.enter array.args).setReg accumulator (BitVec.ofNat w seed)
      have baseValue : start.eval (.var 0) = array.base :=
        State.setReg_ne (entry.enter array.args) accumulator 0 (BitVec.ofNat w seed) (Ne.symm ha0)
      have lengthValue :
          (start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1) =
            array.length :=
        (State.setReg_ne start registers.pointer 1 (start.eval (.var 0)) (Ne.symm hp1)).trans
          (State.setReg_ne (entry.enter array.args) accumulator 1
            (BitVec.ofNat w seed) (Ne.symm ha1))
      have pre : ArrayRep start.mem (start.eval (.var 0)) xs ∧
          ((start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1)).toNat = xs.length ∧
          (start.eval (.var 0)).toNat + xs.length ≤ heapLimit ∧
          (start.eval (.var 0)).toNat + xs.length < 2 ^ w ∧ I (start.regs registers.accumulator) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simpa only [baseValue] using represented.2.1
        · simpa only [lengthValue] using represented.1
        · simpa only [baseValue] using represented.2.2
        · simpa only [baseValue] using fit
        · simpa only [start, State.setReg_same, registers, registersOfNodup] using initial
      have bounded := Call.forIn_timeBound_of_step registers hw lookup correct time preserve
        xs admissible (base := .var 0) (length := .var 1) start pre _ callee
        (by simpa only [Call.body, registers, registersOfNodup] using traversal)
      have accumulatorValue : start.regs registers.accumulator = BitVec.ofNat w seed :=
        State.setReg_same (entry.enter array.args) accumulator (BitVec.ofNat w seed)
      dsimp only at bounded
      rw [accumulatorValue] at bounded
      change _ ≤ 1 + 1 +
        (xs.mapIdx (fun i x => C ((xs.take i).foldl step (BitVec.ofNat w seed)) x)).sum +
        (Fold.Call.callSteps control helper [.var accumulator, .var element] 0 + 14) *
          xs.length + 4 at bounded
      change 2 + _ ≤
        (xs.mapIdx (fun i x => C ((xs.take i).foldl step (BitVec.ofNat w seed)) x)).sum +
        (Fold.Call.callSteps control helper [.var accumulator, .var element] 0 + 14) *
          xs.length + 8
      omega

end Ram.Source.Array.ForIn
