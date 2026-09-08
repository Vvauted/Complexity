/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Complexity.Computability.Ram.Array.Fold.Call
import Complexity.Computability.Ram.Array.Ref
import Examples.Ram.LocalBindings

/-!
# Folding an array through a proved function

The `sumSquares` function in `LocalBindings.functions` calls `addSquare` for
each represented word. That step calls the existing `square` function; neither
the traversal proof nor the mathematical specification supplies a second
squaring implementation. The specification is the ordinary natural-number sum
of the squared decoded words, encoded back into the word range.
-/

namespace Ram.Examples.ArrayFold

open LocalBindings
open Source Source.Array

/-- The named cursor and accumulator of the one declared implementation. -/
def registers : Fold.Registers :=
  ⟨functions.localReg.sumSquares.xs.base, functions.localReg.sumSquares.xs.length,
    functions.localReg.sumSquares.accumulator, by decide, by decide, by decide⟩

/-- Argument expressions selected from the actual call site, not a second step. -/
def callArguments : List Expr :=
  match functions.function.sumSquares.body with
  | .seq _ (.while _ (.seq (.call _ _ args) _)) => args
  | _ => []

/-- The library's call-based fold is exactly this function's declared body. -/
theorem body_eq : functions.function.sumSquares.body =
    .seq (.assign registers.accumulator (.const 0))
      (Fold.Call.loop registers functions.functionIndex.addSquare callArguments) := rfl

/-- The word-valued fold is the encoded ordinary sum of natural squares.
This equation uses list homomorphisms, independently of a machine execution. -/
theorem foldl_addSquare (xs : List (Word w)) :
    xs.foldl (fun accumulator x => accumulator + x * x) 0 =
      BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum := by
  have squares : (xs.map (fun x => x.toNat ^ 2)).map (BitVec.ofNat w) =
      xs.map (fun x => x * x) := by
    simp [List.map_map, pow_two, BitVec.ofNat_mul]
  have mapped := List.foldl_map_hom
    (g := BitVec.ofNat w) (f := Nat.add) (f' := fun a b => a + b)
    (a := 0) (l := xs.map (fun x => x.toNat ^ 2))
    (fun a b => (BitVec.ofNat_add a b).symm)
  rw [squares, List.foldl_map] at mapped
  simpa only [List.sum_eq_foldl] using mapped

/-- Cursor safety, termination and framing come from the shared fold rule.
The step proof is the existing function contract, not an expanded square body. -/
theorem body_safe {heapLimit : Nat} (hw : 0 < w) (s : Source.State w)
    (base : Word w) (xs : List (Word w))
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec functions.program heapLimit 2 functions.function.sumSquares.body s t ∧
      t.regs registers.accumulator = BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev := by
  let initialized := s.setReg registers.accumulator 0
  obtain ⟨t, execution, result, _, _, _, memory, input, output, _⟩ :=
    Fold.Call.loop_safe registers (args := callArguments) (R := fun _ => True)
      hw functions.function_lookup.addSquare (addSquare_contract heapLimit)
      (fun current _ address arg member => by
        simp only [callArguments, functions.body_eq.sumSquares,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · trivial
        · exact ⟨trivial, address⟩)
      (fun _ _ _ => rfl) (fun _ _ => trivial)
      initialized base xs trivial represented (by exact pointer) (by exact count) heap fit
  refine ⟨t, ?_, ?_, memory, input, output⟩
  · rw [body_eq]
    exact .seq (.assign trivial) execution
  · change t.regs registers.accumulator =
      xs.foldl (fun accumulator x => accumulator + x * x) 0 at result
    exact result.trans (foldl_addSquare xs)

/-- The function returns the mathematical sum of squares through its word
encoding and preserves caller state. No stream driver or time bound is needed. -/
theorem function_contract {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract functions.program heapLimit 2 functions.function.sumSquares
      (fun args entry => args = functions.arguments.sumSquares array ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum ∧ finish = entry) := by
  rintro args entry ⟨rfl, represented⟩
  obtain ⟨callee, execution, returned, memory, input, output⟩ :=
    body_safe hw (entry.enter (functions.arguments.sumSquares array)) array.base xs
      represented.2.1 rfl represented.1 represented.2.2 fit
  have restored : entry.restore callee = entry := by
    simp only [State.restore, memory, input, output, State.enter]
  refine ⟨_, entry, ?_, rfl, rfl⟩
  have invocation := FunctionExec.of_body (f := functions.function.sumSquares)
    (functions.arguments_length.sumSquares array) (by decide) execution (by trivial)
  change callee.eval functions.function.sumSquares.result = _ at returned
  simpa only [returned, restored] using invocation

/-- Observe the same implemented function using an ordinary list expression. -/
theorem eval_eq {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.sumSquares array heapLimit entry =
      Part.some (BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum, entry) := by
  obtain ⟨value, finish, equation, rfl, rfl⟩ :=
    (function_contract hw fit).eval_spec ⟨rfl, represented⟩
  exact equation

/-- When the mathematical sum fits, the decoded result is exactly that natural
number. The modular theorem above does not assume intermediate no-overflow. -/
theorem eval_toNat {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry)
    (resultFit : (xs.map (fun x => x.toNat ^ 2)).sum < 2 ^ w) :
    (functions.eval.sumSquares array heapLimit entry).map (fun result => result.1.toNat) =
      Part.some (xs.map (fun x => x.toNat ^ 2)).sum := by
  rw [eval_eq hw fit represented]
  simp only [Part.map_some, Word.ofNat_toNat_of_lt resultFit]

/-- Each iteration includes the actual helper call, cursor and control flow.
This proof uses the callee's separate cost theorem, not its result equation. -/
theorem body_localMeasured {control heapLimit : Nat} (hw : 0 < w)
    {s t : Source.State w}
    (execution : SafeExec functions.program heapLimit 2 functions.function.sumSquares.body s t) :
    LocalMeasuredExec control functions.program heapLimit 2 functions.function.sumSquares.body
      (74 * (s.regs registers.remaining).toNat + 4) s t := by
  rw [body_eq] at execution ⊢
  cases execution with
  | seq first rest =>
      cases first with
      | assign reads =>
          have loop := Fold.Call.loop_localMeasured registers (control := control)
            hw functions.function_lookup.addSquare addSquare_body_steps rest
          have sequence := LocalMeasuredExec.seq
            (LocalMeasuredExec.assign (control := control) reads) loop
          have callCount : Fold.Call.callSteps control functions.function.addSquare
              callArguments 23 = 63 := by
            rw [Fold.Call.callSteps_eq]
            rfl
          have steps :
              LocalCompiler.stmtSize control (LocalCompiler.calleeLocals functions.program)
                  (.assign registers.accumulator (.const 0)) +
                ((63 + 11) * ((s.setReg registers.accumulator (s.eval (.const 0))).regs
                  registers.remaining).toNat + 2) =
                74 * (s.regs registers.remaining).toNat + 4 := by
            change 2 + ((63 + 11) * (s.regs registers.remaining).toNat + 2) = _
            omega
          simpa only [callCount, steps] using sequence

/-- Body time is observed from the terminating implementation and then
identified by the independent loop count. It includes both nested calls. -/
theorem bodyTime_eq {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    functions.bodyTime.sumSquares array heapLimit entry = Part.some (74 * xs.length + 4) := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract hw fit (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  obtain ⟨steps, measured⟩ := execution.exists_measured functions.registers
  have count : steps = 74 * xs.length + 4 := by
    obtain ⟨_, _, callee, body, _, _, _⟩ := measured
    have same := (body.deterministic (body_localMeasured hw body.erase)).1
    simpa only [show ((entry.enter (functions.arguments.sumSquares array)).regs
      registers.remaining).toNat = xs.length from represented.1] using same
  exact count ▸ measured.bodyTime_eq_some

/-- Execute the same declared fold on a preloaded array. The projection retains
the returned word, full call count and stopping reason; it performs no list loading. -/
def runSumSquares (array : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32) :
    Option (Nat × Nat × StopReason) :=
  (functions.run.sumSquares array heapLimit entry).map fun result =>
    ((result.state.regs 0).toNat, result.steps, result.reason)

/-- The executable function application returns that list sum and the complete
machine count, including its enclosing call and halt. Memory is preloaded;
stack capacity is a safety premise, not a proposed execution budget. -/
theorem runSumSquares_eq {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + 3 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    runSumSquares array heapLimit entry =
      some ((xs.map (fun x => x.toNat ^ 2)).sum % 2 ^ 32, 74 * xs.length + 42, .halted) := by
  let code := LocalCompiler.rawLink functions.registers functions.program
    (LocalCompiler.Function.trampoline functions.functionIndex.sumSquares
      functions.function.sumSquares.params)
  have hcompile : LocalCompiler.Function.compile functions.registers functions.program
      functions.functionIndex.sumSquares functions.function.sumSquares.params = some code := by
    decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  obtain ⟨value, finish, execution, rfl, rfl⟩ := function_contract (by decide : 0 < 32) fit
    (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  obtain ⟨target, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_execution hcompile
      functions.function_lookup.sumSquares hcode hstack execution
      (bodyTime_eq (by decide : 0 < 32) fit represented)
  have count : LocalCompiler.Function.callSteps functions.registers
      functions.function.sumSquares (74 * xs.length + 4) + 1 = 74 * xs.length + 42 := by
    simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
    decide
  simp only [runSumSquares, functions.run.sumSquares,
    max_eq_right (by decide : 1 ≤ functions.registers), returned, Option.map_some, value,
    BitVec.toNat_ofNat, count]

-- The three preloaded words are 1, 2, 3. Every visited word triggers both
-- addSquare and the existing square function; these are real compiled calls.
#eval runSumSquares ⟨0, 3⟩ 3
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }

end Ram.Examples.ArrayFold
