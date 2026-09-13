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
import Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendCost

/-!
# Uniform RAM time of the native record append

The program is the same `program% NativeAppend.append` selected in the source
example. Its generated record projections reuse the shared binary-call bridge;
its fixed input boundary reuses the executable packing bridge. The existing
array append supplies allocation, copying and their linear cost. No second
append implementation, register proof or host conversion is provided.

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

private theorem native_costBound (left right : Array Nat) (w limit : Nat) :
    FunctionArenaCostBound NativeAppend.Source.program
      (NativeAppend.Source.program.body NativeAppend.Source.appendId)
      (fun pair : Buffer .nat × Buffer .nat => Env.cons pair Env.empty)
      (fun pair heap => pair.1.Contents heap left ∧ pair.2.Contents heap right)
      w limit 2 (fun _ => nativeBodyBound (left.size + right.size)) := by
  apply FunctionArenaCostBound.of_stmt
  intro pair heap allowed
  exact Program.Uncurry.call_costBound_imported
    NativeAppend.Source.imports.Complexity.Language.Buffer.Copy.embedding
    Buffer.Copy.appendId rfl (BufferCopy.append_costBound left right w limit)
    ⟨Env.cons pair Env.empty, heap⟩ pair rfl allowed

private theorem append_measured (input : AppendInput) (w : Nat)
    (admitted : Program.width 1 input ≤ w) :
    ArenaMeasured append.source w (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 3
      (append.source.body append.fn)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨append.args input, Input.heap input⟩ (RamInput.cursor input) := by
  have sourceFits : EnvFits w (Input.args input) := by
    intro τ v
    exact RamInput.fits input w (Program.width_base admitted) v
  have pairFits : ValueFits (τ := .prod (.buffer .nat) (.buffer .nat)) w
      ((Input.args input).head, (Input.args input).tail.head) :=
    ⟨sourceFits .here, sourceFits (.there .here)⟩
  have library := Program.arrayPair_append_arenaMeasured input.left input.right
    (by decide : 1 ≤ 1) admitted
  have libraryReturned : ArenaMeasured Buffer.Copy.program w
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 1
      (Buffer.Copy.program.body Buffer.Copy.appendId)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨Input.args input, Input.heap input⟩ (RamInput.cursor input) := by
    apply library.mono_post
    rintro _ _ _ _ ⟨value, returned, _⟩
    exact ⟨value, returned, trivial⟩
  have native := Program.Uncurry.call_measured_imported
    NativeAppend.Source.imports.Complexity.Language.Buffer.Copy.embedding
    Buffer.Copy.appendId rfl
    (P := fun _ _ _ _ => True)
    ⟨Env.cons ((Input.args input).head, (Input.args input).tail.head) Env.empty,
      Input.heap input⟩ pairFits libraryReturned
  have nativeReturned : ArenaMeasured NativeAppend.Source.program w
      (Ram.LanguageCompiler.ArrayFunction.heapLimit w) 2
      (NativeAppend.Source.program.body NativeAppend.Source.appendId)
      (fun _ control _ _ => ∃ value, control = .returned value ∧ True)
      ⟨Env.cons (inputPacking.eval (Input.args input)) Env.empty, Input.heap input⟩
      (RamInput.cursor input) := by
    apply native.mono_post
    rintro _ _ _ _ ⟨value, _, returned, _⟩
    exact ⟨value, returned, trivial⟩
  have packingFits : inputPacking.Fits w (Input.args input) := ⟨pairFits, pairFits⟩
  have packed := inputPacking.program_measured NativeAppend.Source.program
    NativeAppend.Source.appendId rfl (Input.args input) (Input.heap input)
    (P := fun _ _ _ _ => True) packingFits nativeReturned
  apply packed.mono_post
  rintro _ _ _ _ ⟨value, _, returned, _⟩
  exact ⟨value, returned, trivial⟩

private theorem append_costBound (input : AppendInput) (w limit : Nat) :
    StmtArenaCostBound append.source w limit 3 (append.source.body append.fn)
      ⟨append.args input, Input.heap input⟩
      (appendBodyBound (input.left.size + input.right.size)) := by
  have callee : FunctionArenaCostBound NativeAppend.Source.program
      (NativeAppend.Source.program.body NativeAppend.Source.appendId)
      (fun pair : Buffer .nat × Buffer .nat =>
        Env.cons (inputPacking.eval (Buffer.Copy.append_args pair.1 pair.2)) Env.empty)
      (fun pair heap => pair.1.Contents heap input.left ∧ pair.2.Contents heap input.right)
      w limit 2 (fun _ => nativeBodyBound (input.left.size + input.right.size)) :=
    native_costBound input.left input.right w limit
  intro finish control execution cursor finalCursor ready steps counted
  exact inputPacking.program_stmt_costBound NativeAppend.Source.program
    NativeAppend.Source.appendId rfl callee
    ((Input.args input).head, (Input.args input).tail.head) (Input.heap input)
    (Program.arrayPair_contents input.left input.right) execution ready counted

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
