/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Program
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInputResources
import Complexity.Computability.Ram.Compiler.Language.Program.Asymptotics
import Complexity.Computability.Ram.Compiler.Language.Program.Time
import Complexity.Computability.Ram.Compiler.Language.Program.WrapperTactic
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendCost
import Complexity.Computability.Ram.Compiler.Language.Buffer.GetD.Ready
import Complexity.Computability.Ram.Compiler.Language.Buffer.Ragged.GetD.Ready
import Complexity.Computability.Ram.Compiler.Language.Program.InputResources
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceTime
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceAsymptotics

/-!
# Uniform RAM time and space of native record programs

The program is the same `program% NativeAppend.append` selected in the source
example. Shared composition follows its actual generated packing, projections
and calls. The existing array append supplies allocation, copying and their
linear cost. No second append implementation, register proof or host conversion
is provided.

The complete time theorem covers every mathematical input at every admitted
word width. The shared width rules discharge input ranges, output allocation,
code and stack capacity without adding them to the task's precondition.

For append, the preloaded input reservation is linear in the two array lengths.
The actual instruction bound therefore also bounds the union of that reservation
and all addresses accessed by the same invocation. The combined theorem retains
its mathematical output, time and physical space in one execution. This is a
conservative distinct-address footprint, not exact peak-live storage or a charge
for input loading.

The lookup consumer combines two defaulted scalar reads and a branch at the
actual intermediate heap. Its constant bound is for the preloaded invocation,
including generated packing and calls, not for loading an entire input array.
-/

namespace Complexity.Examples.TypedProgram

open Language Program Ram.LanguageCompiler

private def appendCost (size : Nat) : { bound : Nat //
    ∀ (input : AppendInput) (w limit : Nat), input.left.size + input.right.size = size →
      StmtArenaCostBound append.source w limit 3 (append.source.body append.fn)
        ⟨append.args input, Input.heap input⟩ bound } :=
  ⟨_, by
    intro input w limit sized
    have contents := Program.arrayPair_contents input.left input.right
    have bounded := BufferCopy.append_costBound input.left input.right w limit
    rw [sized] at bounded
    program_wrapper_cost [bounded]⟩

private def appendBodyBound (size : Nat) : Nat := (appendCost size).val

private theorem append_measured (input : AppendInput) (w : Nat)
    (admitted : Program.width 1 input ≤ w) :
    ArenaMeasured append.source w (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 3
      (append.source.body append.fn)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨append.args input, Input.heap input⟩ (RamInput.cursor input) := by
  have sourceFits : EnvFits w (Input.args input) := by
    intro τ v
    exact RamInput.fits input w (Program.width_base admitted) v
  program_wrapper_measured [Program.arrayPair_append_arenaMeasured
    input.left input.right (by decide : 1 ≤ 1) admitted]

private theorem append_costBound (input : AppendInput) (w limit : Nat) :
    StmtArenaCostBound append.source w limit 3 (append.source.body append.fn)
      ⟨append.args input, Input.heap input⟩
      (appendBodyBound (input.left.size + input.right.size)) := by
  exact (appendCost _).property input w limit rfl

private theorem appendBodyBound_linear :
    Asymptotics.IsBigO Filter.atTop (fun n => (appendBodyBound n : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  unfold appendBodyBound appendCost
  program_time_asymptotics [BufferCopy.isBigO_appendBodyBound,
    (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).isBigO.natCast_atTop]

/-- The actual high-level record program, including its packing entry, has
uniform linear word-RAM time on all inputs, with no finite-capacity precondition. -/
theorem append_timeO :
    append.TimeO (fun _ => True) (fun input => input.left.size + input.right.size)
      (fun n => n) := by
  apply Program.TimeO.of_measured_auto (depth := 3) (overhead := 1)
    (bound := appendBodyBound) (P := fun _ _ _ _ _ => True)
  · intro input _ w admitted
    exact append_measured input w admitted
  · intro input _ w _
    exact append_costBound input w _
  · program_time_asymptotics [appendBodyBound_linear,
      (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).isBigO.natCast_atTop]

/-- The original record append has uniform linear physical space, including its
preloaded input prefix and every address touched by the actual invocation.
The bound counts distinct addresses, not the capacity of the word address space. -/
theorem append_spaceO :
    append.SpaceO (fun _ => True) (fun input => input.left.size + input.right.size)
      (fun n => n) := by
  apply Program.SpaceO.of_time (inputBound := fun n => 1 + n) append_timeO
  · intro input _
    change RamInput.cursor (input.left, input.right) ≤
      1 + (input.left.size + input.right.size)
    rw [RamInput.arrayPair_cursor]
    omega
  · program_space_asymptotics
      [Asymptotics.isBigO_refl (fun n : Nat => (n : ℝ)) Filter.atTop,
        (Asymptotics.isLittleO_const_id_atTop (1 : ℝ)).isBigO.natCast_atTop]

/-- Correctness and both uniform resource bounds hold for the same original
append invocation and its actual returned value and final heap. No additional
input-range, capacity or termination promise is required. -/
theorem append_time_space_correct :
    ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
      Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
        (fun n : Nat => (n : ℝ)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
        (fun n : Nat => (n : ℝ)) ∧
      ∀ input : AppendInput, ∀ w, Program.width overhead input ≤ w →
        ∃ depth, ∃ execution : append.Execution input w depth,
          (∃ output, execution.Represents output ∧
            output.values = input.left ++ input.right) ∧
          execution.result.steps ≤ timeBound (input.left.size + input.right.size) ∧
          execution.spaceWords ≤ spaceBound (input.left.size + input.right.size) := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ :=
    append_timeO.runs_space_correct append_spaceO append_correct
  exact ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic,
    fun input w admitted => runs input trivial w admitted⟩

private def lookupCost : { bound : Nat //
    ∀ (input : LookupInput) (w limit : Nat),
      StmtArenaCostBound lookup.source w limit 2 (lookup.source.body lookup.fn)
        ⟨lookup.args input, Input.heap input⟩ bound } := ⟨_, by
  intro input w limit
  program_wrapper_cost [Buffer.GetD.getNat_arenaCostBound w limit 0,
    Buffer.GetD.getBool_arenaCostBound w limit 0]⟩

private theorem lookup_measured (input : LookupInput) (w : Nat)
    (admitted : Program.width 1 input ≤ w) :
    ArenaMeasured lookup.source w (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 2
      (lookup.source.body lookup.fn)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨lookup.args input, Input.heap input⟩ (RamInput.cursor input) := by
  have sourceFits : EnvFits w (Input.args input) :=
    RamInput.fits input w (Program.width_base admitted)
  have observed := Input.represented input
  have contents : (Input.args input).head.Contents (Input.heap input) input.values ∧
      (Input.args input).tail.head.Contents (Input.heap input) input.enabled :=
    ⟨observed.1, observed.2.1⟩
  have indexFits : input.index < 2 ^ w := sourceFits (.there (.there .here))
  have fallbackFits : input.fallback < 2 ^ w := sourceFits (.there (.there (.there .here)))
  have resultFits := RamInput.getD_fits input admitted contents.1 input.index
    input.fallback fallbackFits
  have natural := Buffer.GetD.getNat_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input) input.values input.index input.fallback
    (Input.args input).head (Input.heap input) contents.1 (sourceFits .here)
    indexFits fallbackFits resultFits
  have boolean := Buffer.GetD.getBool_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input)
    (Ram.LanguageCompiler.ArrayFunction.width_pos (Program.width_base admitted))
    input.enabled input.index false (Input.args input).tail.head (Input.heap input)
    contents.2 (sourceFits (.there .here)) indexFits
  program_wrapper_measured [natural, boolean]

/-- The existing high-level lookup has constant uniform word-RAM invocation
time, including both defaulted reads and generated wrapper calls. Input arrays
are preloaded by `Program.TimeO`; parsing or constructing them is not free work
claimed by this theorem. No valid-index or extra element-range promise is used. -/
theorem lookup_timeO :
    lookup.TimeO (fun _ => True) (fun input => input.values.size + input.enabled.size)
      (fun _ => 1) := by
  apply Program.TimeO.of_measured_auto (depth := 2) (overhead := 1)
    (bound := fun _ => lookupCost.val) (P := fun _ _ _ _ _ => True)
  · intro input _ w admitted
    exact lookup_measured input w admitted
  · intro input _ w _
    exact lookupCost.property input w _
  · simp only [Nat.cast_one]
    program_time_asymptotics
      [Asymptotics.isBigO_refl (fun _ : Nat => (1 : ℝ)) Filter.atTop]

private def raggedLookupCost : { bound : Nat //
    ∀ (input : RaggedLookupInput) (w limit : Nat),
      StmtArenaCostBound raggedLookup.source w limit 2
        (raggedLookup.source.body raggedLookup.fn)
        ⟨raggedLookup.args input, Input.heap input⟩ bound } := ⟨_, by
  intro input w limit
  program_wrapper_cost [Buffer.Ragged.GetD.getNat_arenaCostBound w limit 0,
    Buffer.Ragged.GetD.getBool_arenaCostBound w limit 0,
    Buffer.GetD.getNat_arenaCostBound w limit 0,
    Buffer.GetD.getBool_arenaCostBound w limit 0]⟩

private theorem raggedLookup_measured (input : RaggedLookupInput) (w : Nat)
    (admitted : Program.width 1 input ≤ w) :
    ArenaMeasured raggedLookup.source w (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 2
      (raggedLookup.source.body raggedLookup.fn)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨raggedLookup.args input, Input.heap input⟩ (RamInput.cursor input) := by
  have sourceFits : EnvFits w (Input.args input) :=
    RamInput.fits input w (Program.width_base admitted)
  have positive := Ram.LanguageCompiler.ArrayFunction.width_pos (Program.width_base admitted)
  have observed := Input.represented input
  have values : (Representation.raggedArray .nat).Rel input.values
      ((Input.args input).head, (Input.args input).tail.head) (Input.heap input) :=
    ⟨observed.1, observed.2.1⟩
  have flags : (Representation.raggedArray .bool).Rel input.flags
      ((Input.args input).tail.tail.head, (Input.args input).tail.tail.tail.head)
      (Input.heap input) := ⟨observed.2.2.1, observed.2.2.2.1⟩
  have fallback : (Input.args input).tail.tail.tail.tail.head.Contents
      (Input.heap input) input.fallback := observed.2.2.2.2.1
  have fallbackFlags : (Input.args input).tail.tail.tail.tail.tail.head.Contents
      (Input.heap input) input.fallbackFlags := observed.2.2.2.2.2.1
  have valueCount := Representation.raggedArray_length values
  have flagCount := Representation.raggedArray_length flags
  dsimp only at valueCount flagCount
  change (Input.args input).head.Contents (Input.heap input) input.values.flattenOffsets ∧
    (Input.args input).tail.head.Contents (Input.heap input) input.values.flatten at values
  change (Input.args input).tail.tail.head.Contents
      (Input.heap input) input.flags.flattenOffsets ∧
    (Input.args input).tail.tail.tail.head.Contents (Input.heap input) input.flags.flatten at flags
  have valueRanges : (Input.args input).head.length < 2 ^ w ∧
      (Input.args input).tail.head.length < 2 ^ w :=
    ⟨sourceFits .here, sourceFits (.there .here)⟩
  have flagRanges : (Input.args input).tail.tail.head.length < 2 ^ w ∧
      (Input.args input).tail.tail.tail.head.length < 2 ^ w :=
    ⟨sourceFits (.there (.there .here)), sourceFits (.there (.there (.there .here)))⟩
  have payloadFits : input.values.flatten.size < 2 ^ w := by
    rw [values.2.size_eq]; exact valueRanges.2
  have flagPayloadFits : input.flags.flatten.size < 2 ^ w := by
    rw [flags.2.size_eq]; exact flagRanges.2
  have rowFits : input.row < 2 ^ w :=
    sourceFits (.there (.there (.there (.there (.there (.there .here))))))
  have columnFits : input.column < 2 ^ w :=
    sourceFits (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let row := Buffer.Ragged.GetD.getView (kind := .nat) input.values input.row
    ((Input.args input).head, (Input.args input).tail.head)
    (Input.args input).tail.tail.tail.tail.head
  let flagRow := Buffer.Ragged.GetD.getView (kind := .bool) input.flags input.row
    ((Input.args input).tail.tail.head, (Input.args input).tail.tail.tail.head)
    (Input.args input).tail.tail.tail.tail.tail.head
  have rowContents : row.Contents (Input.heap input) (input.values.getD input.row input.fallback) :=
    Buffer.Ragged.GetD.getView_contents (kind := .nat) (rows := input.values)
      (storage := ((Input.args input).head, (Input.args input).tail.head))
      values fallback input.row
  have flagContents : flagRow.Contents (Input.heap input)
      (input.flags.getD input.row input.fallbackFlags) :=
    Buffer.Ragged.GetD.getView_contents (kind := .bool) (rows := input.flags)
      (storage := ((Input.args input).tail.tail.head, (Input.args input).tail.tail.tail.head))
      flags fallbackFlags input.row
  have rowLengthFits : row.length < 2 ^ w := Buffer.Ragged.GetD.getView_length_fits
    payloadFits (sourceFits (.there (.there (.there (.there .here))))) input.row
  have flagLengthFits : flagRow.length < 2 ^ w := Buffer.Ragged.GetD.getView_length_fits
    flagPayloadFits (sourceFits (.there (.there (.there (.there (.there .here)))))) input.row
  have zeroFits : 0 < 2 ^ w := by positivity
  have resultFits := RamInput.getD_fits input admitted rowContents input.column 0 zeroFits
  have naturalRow := Buffer.Ragged.GetD.getNat_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input) positive input.values input.row input.fallback
    ((Input.args input).head, (Input.args input).tail.head)
    (Input.args input).tail.tail.tail.tail.head (Input.heap input)
    values fallback (by omega) payloadFits rowFits
    (sourceFits (.there (.there (.there (.there .here)))))
  have booleanRow := Buffer.Ragged.GetD.getBool_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input) positive input.flags input.row input.fallbackFlags
    ((Input.args input).tail.tail.head, (Input.args input).tail.tail.tail.head)
    (Input.args input).tail.tail.tail.tail.tail.head (Input.heap input)
    flags fallbackFlags (by omega) flagPayloadFits rowFits
    (sourceFits (.there (.there (.there (.there (.there .here))))))
  have natural := Buffer.GetD.getNat_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input) (input.values.getD input.row input.fallback) input.column 0
    row (Input.heap input) rowContents rowLengthFits columnFits zeroFits resultFits
  have boolean := Buffer.GetD.getBool_arenaMeasured
    (heapLimit := Ram.LanguageCompiler.ArrayFunction.heapLimit w) (depth := 0)
    (cursor := RamInput.cursor input) positive (input.flags.getD input.row input.fallbackFlags)
    input.column false flagRow (Input.heap input) flagContents flagLengthFits columnFits
  -- Three input-bounded quantities fit after two additional bits. The uniform
  -- policy supplies these bits; no new promise is imposed on mathematical inputs.
  have sumFits : (input.values.getD input.row input.fallback).getD input.column 0 +
      input.values.size + row.length < 2 ^ w := by
    let base := Program.width 0 input
    have baseFits : EnvFits base (Input.args input) :=
      RamInput.fits input base (Program.width_base (le_refl base))
    have baseRanges : (Input.args input).head.length < 2 ^ base ∧
        (Input.args input).tail.head.length < 2 ^ base :=
      ⟨baseFits .here, baseFits (.there .here)⟩
    have smallPayload : input.values.flatten.size < 2 ^ base := by
      rw [values.2.size_eq]; exact baseRanges.2
    have smallRow : row.length < 2 ^ base := Buffer.Ragged.GetD.getView_length_fits
      smallPayload (baseFits (.there (.there (.there (.there .here))))) input.row
    have smallResult : (input.values.getD input.row input.fallback).getD input.column 0 <
        2 ^ base := RamInput.getD_fits input (le_refl base) rowContents input.column 0
          (by change 0 < 2 ^ base; positivity)
    have basePositive := Ram.LanguageCompiler.ArrayFunction.inputWordWidth_pos (RamInput.words input)
    have baseEq : base = Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (RamInput.words input) + 1 := by
      simp only [base, Program.width, Language.ArrayFunction.width, Nat.zero_add, Nat.one_mul]
    have extra : base + 2 ≤ w := by
      change 2 * (Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (RamInput.words input) + 1) ≤ w at admitted
      omega
    have enlarged : 2 ^ base * 4 ≤ 2 ^ w := by
      simpa only [Nat.pow_add, show 2 ^ 2 = 4 from rfl] using
        (Nat.pow_le_pow_right (by decide : 0 < 2) extra)
    omega
  dsimp only [row] at sumFits rowLengthFits
  change ((Input.args input).get .here).length = input.values.size + 1 at valueCount
  program_wrapper_measured [naturalRow, booleanRow, boolean, natural]
  all_goals omega

/-- Borrowed row selection followed by scalar lookup has constant invocation
time, even for empty or missing rows. Packing, calls, the branch and final
arithmetic are included; constructing the preloaded input is not. -/
theorem raggedLookup_timeO :
    raggedLookup.TimeO (fun _ => True) (fun input => input.values.size + input.flags.size)
      (fun _ => 1) := by
  apply Program.TimeO.of_measured_auto (depth := 2) (overhead := 1)
    (bound := fun _ => raggedLookupCost.val) (P := fun _ _ _ _ _ => True)
  · intro input _ w admitted
    exact raggedLookup_measured input w admitted
  · intro input _ w _
    exact raggedLookupCost.property input w _
  · simp only [Nat.cast_one]
    program_time_asymptotics
      [Asymptotics.isBigO_refl (fun _ : Nat => (1 : ℝ)) Filter.atTop]

end Complexity.Examples.TypedProgram
