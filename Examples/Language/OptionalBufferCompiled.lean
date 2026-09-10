/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.OptionalBuffer
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.Linking.Tactic
import Mathlib.Data.Prod.Basic

/-!
# Executing imported structured results and an optional borrowed buffer

The same source call chain returns a nested mathematical product/option, slices
the original buffer, and uses the returned optional view for a real read and
write. Existing source contracts identify the actual imported results and heaps;
the additional proofs check word ranges and sufficient call nesting.

Independent structural cost bounds count the emitted field copies, option
dispatch, imported calls and buffer operations. The shared typed execution rule
retains the real halted runner, its four return fields and its actual final
memory. No buffer is manufactured for `none`, and no source object is copied or
allocated. The invocation assumes preloaded represented input and adequate code
and stack capacity; input loading is outside this boundary.
-/

namespace Complexity.Language.Examples.OptionalBuffer

open Ram.LanguageCompiler

/-- The native structured helper needs no nested call. Its optional tag and
both actual payload fields fit whenever the input does and the width is positive. -/
theorem classifyLength_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Metadata.program w 0 Metadata.classifyLengthId
      (Metadata.classifyLength_onArgs fun n _ => n < 2 ^ w) := by
  have tagFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (n)
  all_goals simp_all

/-- A uniform body bound, checked against the compiler's primitive, branch,
structured-return and initialization charges. -/
theorem classifyLength_costBound :
    FunctionCostBound Metadata.program Metadata.classifyLengthId (fun _ _ => True)
      (fun _ _ => 26) := by
  ram_source_cost (n)
  all_goals omega

/-- The inspector reuses the pure imported contract at its actual returned
option. Its full-length slice needs one nested call and no heap assumption. -/
theorem inspect_realizable {w : Nat} (hw : 0 < w) :
    FunctionRealizable Library.program w 1 Library.inspectId
      (Library.inspect_onArgs fun xs _ => xs.length < 2 ^ w) := by
  have tagFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (xs)
  by_cases empty : xs.length = 0
  · ram_source_call using (classifyLength_realizable hw), classifyLength_total
      via Library.imports.Metadata.embedding
    all_goals simp_all [Prod.eq_iff_fst_eq_snd_eq] <;> omega
  · ram_source_call using (classifyLength_realizable hw), classifyLength_total
      via Library.imports.Metadata.embedding
    all_goals simp_all [Prod.eq_iff_fst_eq_snd_eq] <;> omega

/-- The imported helper's real call overhead plus the inspector's field,
slice, match and return charges. This is a body bound, not a source budget. -/
def inspectBodyBound : Nat := callCost Metadata.program Metadata.classifyLengthId 26 + 47

/-- The same inspector's compiler-derived cost includes the imported call and
the actual descriptor construction, with no charge for a nonexistent array copy. -/
theorem inspect_costBound :
    FunctionCostBound Library.program Library.inspectId (fun _ _ => True)
      (fun _ _ => inspectBodyBound) := by
  ram_source_cost (xs) using classifyLength_costBound via Library.imports.Metadata.embedding
  all_goals
    simp only [inspectBodyBound, callCost_embeds Library.imports.Metadata.embedding]
    omega

/-- The only extra arithmetic range concerns the cell that is actually
incremented. Other cells retain the ordinary represented-heap requirement. -/
theorem bump_realizable {w : Nat} (hw : 0 < w) (contents : Array Nat)
    (incrementFits : ∀ h : 0 < contents.size, contents[0] + 1 < 2 ^ w) :
    FunctionRealizable Implementation.program w 2 Implementation.bumpId
      (Implementation.bump_onArgs fun xs heap =>
        xs.Contents heap contents ∧ xs.length < 2 ^ w) := by
  have tagFits : 1 < 2 ^ w := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  ram_source_realize (xs)
  rename_i heap input
  rcases input with ⟨observed, lengthFits⟩
  by_cases empty : xs.length = 0
  · ram_source_call using (inspect_realizable hw), inspect_total
      via Implementation.imports.Library.embedding
    all_goals simp_all [inspectResult] <;> omega
  · have nonempty : 0 < contents.size := by
      have := observed.size_eq
      omega
    have loaded := observed.read nonempty
    have fits := incrementFits nonempty
    have writable (value : Nat) : ∃ finish, heap.write xs 0 value = .ok finish := by
      obtain ⟨finish, written, _⟩ := observed.write_exists nonempty value
      exact ⟨finish, written⟩
    ram_source_call using (inspect_realizable hw), inspect_total
      via Implementation.imports.Library.embedding
    all_goals
      simp_all [inspectResult, Except.ok.injEq] <;>
      first
      | omega
      | exact writable _

/-- The caller includes the actual imported inspector call and its selected
read/update path, including product/option field copies. -/
def bumpBodyBound : Nat := callCost Library.program Library.inspectId inspectBodyBound + 57

/-- This uniform count follows the existing compiler cost rules. It neither
assumes source termination nor reruns the mathematical array-correctness proof. -/
theorem bump_costBound :
    FunctionCostBound Implementation.program Implementation.bumpId (fun _ _ => True)
      (fun _ _ => bumpBodyBound) := by
  ram_source_cost (xs) using inspect_costBound via Implementation.imports.Library.embedding
  all_goals
    simp only [bumpBodyBound, callCost_embeds Implementation.imports.Library.embedding]
    omega

/-- The full invocation bound adds the real outer call, return and final halt. -/
def bumpInvocationBound : Nat :=
  Ram.LocalCompiler.Function.callSteps (programControl Implementation.program)
    (lowerFunc Implementation.program Implementation.bumpId) bumpBodyBound + 1

/-- The verified source operation executes on the real RAM with the same
mathematical value and array update. The independent step bound describes that
same invocation; the shared outcome retains its exact runner and memory facts. -/
theorem bump_execute {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    (xs : Buffer .nat) (contents : Array Nat) {heap : Heap}
    (observed : xs.Contents heap contents)
    (incrementFits : ∀ h : 0 < contents.size, contents[0] + 1 < 2 ^ w)
    {entry : Ram.Source.State w}
    (launch : FunctionLaunch Implementation.program Implementation.bumpId 2 heapLimit placement
      (Implementation.bump_args xs) heap entry) :
    ∃ outcome : FunctionExecution Implementation.program Implementation.bumpId heapLimit placement
        (Implementation.bump_args xs) heap entry,
      bumpPost xs contents heap outcome.value outcome.heap ∧
      outcome.result.steps ≤ bumpInvocationBound := by
  have lengthFits : xs.length < 2 ^ w := by
    have arguments : EnvFits (Γ := [.buffer .nat]) w (Implementation.bump_args xs) :=
      launch.arguments
    exact arguments .here
  obtain ⟨outcome, property, bounded⟩ :=
    (bump_realizable launch.positive contents incrementFits).execute_le (bump_total contents)
      bump_costBound launch ⟨observed, lengthFits⟩ observed trivial
  exact ⟨outcome, property, bounded⟩

/-- The source array contract describes the actual halted machine's memory,
not a separately chosen source execution witness. -/
theorem bump_memory {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    {xs : Buffer .nat} {contents : Array Nat} {heap : Heap} {entry : Ram.Source.State w}
    (outcome : FunctionExecution Implementation.program Implementation.bumpId heapLimit placement
      (Implementation.bump_args xs) heap entry)
    (property : bumpPost xs contents heap outcome.value outcome.heap) :
    Ram.Source.ArrayAt heapLimit (bufferRef placement xs).base
      (objectWords w (τ := .nat) (bumped contents)).toList
        (Ram.Source.State.ofRam outcome.result.state) :=
  outcome.memory.view_arrayAt property.2.1

/-- The same actual invocation returns four fields: length, option tag and
borrowed descriptor. Absence has a zero tag and canonical zero-filled payload,
not a fabricated buffer. This is an observation of the shared result, not a
second execution or a decoder chosen from the specification. -/
theorem bump_returnedValues {w heapLimit : Nat} {placement : Nat → Ram.Word w}
    {xs : Buffer .nat} {contents : Array Nat} {heap : Heap} {entry : Ram.Source.State w}
    (outcome : FunctionExecution Implementation.program Implementation.bumpId heapLimit placement
      (Implementation.bump_args xs) heap entry)
    (property : bumpPost xs contents heap outcome.value outcome.heap) :
    Ram.LocalCompiler.Function.returnedValues 4 outcome.result.state =
      if xs.length = 0 then [0, 0, 0, 0] else
        [BitVec.ofNat w xs.length, BitVec.ofNat w 1,
          Ram.arrayAddr (placement xs.object) xs.offset, BitVec.ofNat w xs.length] := by
  have returned := outcome.returned
  change Ram.LocalCompiler.Function.returnedValues 4 outcome.result.state =
    valueWords placement (τ := .prod .nat (.option (.buffer .nat))) outcome.value at returned
  rw [property.1] at returned
  change Ram.LocalCompiler.Function.returnedValues 4 outcome.result.state =
    valueWords placement (τ := .prod .nat (.option (.buffer .nat)))
      (xs.length, if xs.length = 0 then none else some xs) at returned
  rw [valueWords_prod (α := .nat) (β := .option (.buffer .nat))] at returned
  by_cases empty : xs.length = 0
  · simpa [empty, valueWords_nat, valueWords_none, fieldCount] using returned
  · simp only [if_neg empty] at returned ⊢
    rw [valueWords_some (τ := .buffer .nat), valueWords_nat, valueWords_buffer] at returned
    simpa using returned

end Complexity.Language.Examples.OptionalBuffer
