/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Complexity.Computability.Ram.Array.ForIn.Function
import Examples.Ram.LocalBindings

/-!
# Folding an array through a proved function

The `sumSquares` function in `LocalBindings.functions` calls `addSquare` for
each represented word. That step calls the existing `square` function; neither
the traversal proof nor the mathematical specification supplies a second
squaring implementation. The specification is the ordinary natural-number sum
of the squared decoded words, encoded back into the word range.

The source uses a scoped `for` element binding. Generated body and return
equations select the shared function rule, so this proof does not name the
private cursor, extract call expressions or reconstruct parameter frames.
-/

namespace Ram.Examples.ArrayFold

open LocalBindings
open Source Source.Array

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

/-- The function returns the mathematical sum of squares through its word
encoding and preserves caller state. No stream driver or time bound is needed. -/
theorem function_contract {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract functions.program heapLimit 2 functions.function.sumSquares
      (fun args entry => args = functions.arguments.sumSquares array ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum ∧ finish = entry) := by
  have correct := ForIn.function_contract functions.body_eq.sumSquares
    functions.result_eq.sumSquares rfl (by decide) hw functions.function_lookup.addSquare
    (addSquare_contract heapLimit) array xs fit
  exact correct.consequence (fun _ _ pre => pre)
    (fun _ _ _ _ _ post => ⟨post.1.trans (foldl_addSquare xs), post.2⟩)

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

/-- Body time is observed from the terminating implementation and then
identified by the independent loop count. It includes both nested calls. -/
theorem bodyTime_eq {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    functions.bodyTime.sumSquares array heapLimit entry = Part.some (76 * xs.length + 8) := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract hw fit (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  have time := ForIn.function_bodyTime (control := functions.registers)
    functions.body_eq.sumSquares (by decide) hw functions.function_lookup.addSquare
    addSquare_body_steps array xs represented execution
  change functions.bodyTime.sumSquares array heapLimit entry =
    Part.some (76 * xs.length + 8) at time
  exact time

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
      some ((xs.map (fun x => x.toNat ^ 2)).sum % 2 ^ 32, 76 * xs.length + 67, .halted) := by
  let code := LocalCompiler.rawLink functions.registers functions.program
    (LocalCompiler.Function.trampoline functions.functionIndex.sumSquares
      functions.function.sumSquares.params)
  have hcompile : LocalCompiler.Function.compile functions.registers functions.program
      functions.functionIndex.sumSquares functions.function.sumSquares.params = some code := by
    set_option maxRecDepth 4096 in decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  obtain ⟨value, finish, execution, rfl, rfl⟩ := function_contract (by decide : 0 < 32) fit
    (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  obtain ⟨target, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_execution hcompile
      functions.function_lookup.sumSquares hcode hstack execution
      (bodyTime_eq (by decide : 0 < 32) fit represented)
  have count : LocalCompiler.Function.callSteps functions.registers
      functions.function.sumSquares (76 * xs.length + 8) + 1 = 76 * xs.length + 67 := by
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
