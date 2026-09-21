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

/-!
# Uniform RAM time of the native record append

The program is the same `program% NativeAppend.append` selected in the source
example. Shared composition follows its actual generated packing, projections
and calls. The existing array append supplies allocation, copying and their
linear cost. No second append implementation, register proof or host conversion
is provided.

The complete time theorem covers every mathematical input at every admitted
word width. The shared width rules discharge input ranges, output allocation,
code and stack capacity without adding them to the task's precondition.
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

end Complexity.Examples.TypedProgram
