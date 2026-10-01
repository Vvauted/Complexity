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
import Complexity.Computability.Ram.Compiler.Language.Program.InputResources

/-!
# Uniform RAM time of native record programs

The program is the same `program% NativeAppend.append` selected in the source
example. Shared composition follows its actual generated packing, projections
and calls. The existing array append supplies allocation, copying and their
linear cost. No second append implementation, register proof or host conversion
is provided.

The complete time theorem covers every mathematical input at every admitted
word width. The shared width rules discharge input ranges, output allocation,
code and stack capacity without adding them to the task's precondition.

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

end Complexity.Examples.TypedProgram
