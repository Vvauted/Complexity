/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Program
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInputResources
import Complexity.Computability.Ram.Compiler.Language.Program.Packing
import Complexity.Computability.Ram.Compiler.Language.Program.Time
import Complexity.Computability.Ram.Compiler.Language.Program.Uncurry
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

private abbrev inputPacking := program_packing% append

private abbrev importedAppend :=
  NativeAppend.Source.imports.Complexity.Language.Buffer.Copy.map.toFun Buffer.Copy.appendId

private abbrev importedNative :=
  (SignatureMap.appendRight
    [Program.Packing.signature [.buffer .nat, .buffer .nat] (.buffer .nat)]
    NativeAppend.Source.signatures).toFun NativeAppend.Source.appendId

private def nativeBodyBound (n : Nat) : Nat :=
  Program.Uncurry.callBound NativeAppend.Source.program importedAppend
    (.buffer .nat) (.buffer .nat) (BufferCopy.appendBodyBound n) + 2

private def appendBodyBound (n : Nat) : Nat :=
  inputPacking.callBound append.source importedNative (nativeBodyBound n)

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
  have contents := Program.arrayPair_contents input.left input.right
  unfold appendBodyBound nativeBodyBound
  program_wrapper_cost [BufferCopy.append_costBound input.left input.right w limit]

private theorem appendBodyBound_linear :
    Asymptotics.IsBigO Filter.atTop (fun n => (appendBodyBound n : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  have constant (c : Nat) : Asymptotics.IsBigO Filter.atTop
      (fun _ : Nat => (c : ℝ)) (fun n : Nat => (n : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop (c : ℝ)).isBigO.natCast_atTop
  have bounded := ((BufferCopy.isBigO_appendBodyBound.add
    (constant (Program.Uncurry.callBound NativeAppend.Source.program importedAppend
      (.buffer .nat) (.buffer .nat) 0))).add (constant 2)).add
    (constant (inputPacking.callBound append.source importedNative 0))
  convert bounded using 1
  funext n
  simp only [appendBodyBound, nativeBodyBound]
  rw [Program.Packing.callBound_eq, Program.Uncurry.callBound_eq]
  simp only [Nat.cast_add, Nat.cast_ofNat]

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
  · exact Program.isBigO_invocationBound_linear append appendBodyBound_linear

end Complexity.Examples.TypedProgram
