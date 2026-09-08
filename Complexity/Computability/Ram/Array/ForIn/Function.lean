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
record. The result is an ordinary `List.foldl`, with the caller state unchanged.

`Ram.Source.Array.ForIn.function_bodyTime` separately observes the body count
of a completed invocation, using a theorem about the helper's actual compiled
body. Its count includes iteration and initialization, but not the enclosing
call to the array function itself.

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

/-- A single-array function computes a read-only scalar fold through actual
calls. Generated body/result equations infer every local slot; the layout
premise is a decidable fact about those slots. The helper's contract, not a
host callback, supplies each mathematical accumulator update. -/
theorem function_contract {program : Program} {f helper : Func}
    {accumulator pointer remaining element fn seed heapLimit depth : Nat}
    {step : Word w → Word w → Word w}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call accumulator fn [.var accumulator, .var element])))
    (resultShape : f.result = .var accumulator) (params : f.params = 2)
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup ∧ 2 ≤ f.locals)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (contract : ∀ a x, FunctionContract program heapLimit depth helper
      (fun args _ => args = [a, x])
      (fun _ entry value finish => value = step a x ∧ finish = entry))
    (array : ArrayRef w) (xs : List (Word w))
    (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit (depth + 1) f
      (fun args entry => args = array.args ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = xs.foldl step (BitVec.ofNat w seed) ∧ finish = entry) := by
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
      Call.forIn_safe registers hw lookup contract start xs
        (base := .var 0) (length := .var 1) (by trivial) (by trivial)
        (by simpa only [baseValue] using represented.2.1)
        (by simpa only [lengthValue] using represented.1)
        (by simpa only [baseValue] using represented.2.2)
        (by simpa only [baseValue] using fit)
    rw [bodyShape, Verification.TotalWP.seq_iff, Verification.TotalWP.assign_iff]
    refine ⟨trivial, finish, ?_, ?_⟩
    · simpa only [Call.body, registers, registersOfNodup] using execution
    · refine ⟨?_, ?_, ?_⟩
      · rw [resultShape]
        trivial
      · simpa only [resultShape, State.eval, Expr.eval, start, State.setReg_same,
          registers, registersOfNodup] using result
      · change State.mk entry.regs finish.mem finish.input finish.outputRev = entry
        rw [memory, input, output]
        rfl

/-- The same completed function invocation has the count obtained from the
helper's measured body and its actual call instructions. The surrounding
iteration includes its loads, cursor updates, guards and initialization; the
function also executes the initial accumulator assignment. -/
theorem function_bodyTime {program : Program} {f helper : Func}
    {accumulator pointer remaining element fn seed control heapLimit depth bodySteps : Nat}
    (bodyShape : f.body = .seq (.assign accumulator (.const seed))
      (Stmt.forIn pointer remaining element (.var 0) (.var 1)
        (.call accumulator fn [.var accumulator, .var element])))
    (layout : [0, 1, accumulator, pointer, remaining, element].Nodup)
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth helper.body steps s t → steps = bodySteps)
    (array : ArrayRef w) (xs : List (Word w)) {entry finish : State w} {value : Word w}
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
              (.call accumulator fn [.var accumulator, .var element])))
          (2 + (1 + 1 +
            (Fold.Call.callSteps control helper [.var accumulator, .var element] bodySteps + 14) *
              ((start.setReg registers.pointer (start.eval (.var 0))).eval (.var 1)).toNat + 4))
          (entry.enter array.args) callee at full
        rw [lengthValue, represented.1] at full
        convert full using 1; omega
  exact (FunctionMeasuredExec.of_body arity frame measured resultReads).bodyTime_eq_some

end Ram.Source.Array.ForIn
