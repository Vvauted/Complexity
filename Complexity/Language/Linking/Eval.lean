/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Reflection
import Complexity.Language.Eval.Basic

/-!
# Native source observations after program linking

A checked table embedding preserves the entire partial observation, including
divergence, finite faults and their final heaps. `SignatureMap.eval` presents a
mapped target function at its original parameter and result types. It transports
the existing `Program.eval`; it is not a second evaluator or a host callback.
-/

namespace Complexity.Language

/-- Relocating calls through an actual program embedding preserves the whole
partial observation, not just known successful executions. -/
theorem Stmt.eval_renameCalls {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {Γ : List Ty} {result : Ty} (statement : Stmt source Γ result) (entry : State Γ) :
    (statement.renameCalls map).eval targetProgram entry = statement.eval sourceProgram entry := by
  apply Part.ext
  rintro ⟨finish, control⟩
  simp only [Stmt.mem_eval_iff]
  exact Exec.renameCalls_iff embedded

/-- Observe an actual mapped target function using its original source argument
and result types. Its initial and final shared heap remain explicit. -/
noncomputable def SignatureMap.eval {source target : List Signature}
    (map : SignatureMap source target) (program : Program target)
    (fn : Fin source.length) (args : Env source[fn].params) :
    ExceptT Fault (StateT Heap Part) (Value source[fn].result) :=
  (cast (congrArg
    (fun signature => Env signature.params → ExceptT Fault (StateT Heap Part) (Value signature.result))
    (map.signature_eq fn)) (program.eval (map.toFun fn))) args

/-- Observe the actual selected body at a propositionally equal complete
signature. This is transport of the existing evaluation, including its final
heap and control, not a second evaluator or a heap-independent decoding. -/
theorem Program.eval_cast_eq {signatures : List Signature}
    (program : Program signatures) (fn : Fin signatures.length) {signature : Signature}
    (same : signatures[fn] = signature) (args : Env signature.params) (heap : Heap) :
    (cast (congrArg
      (fun signature => Env signature.params →
        ExceptT Fault (StateT Heap Part) (Value signature.result)) same)
      (program.eval fn)) args heap =
        ((cast (congrArg (fun signature => Stmt signatures signature.params signature.result) same)
          (program.body fn)).eval program ⟨args, heap⟩).map
            (fun outcome => (outcome.2.toExcept, outcome.1.heap)) := by
  cases same
  rfl

/-- A caller may reuse the original native function specification after linking,
without unfolding its loops or recursive calls or re-proving termination. -/
theorem Program.Embeds.eval_eq {source target : List Signature}
    {sourceProgram : Program source} {targetProgram : Program target}
    {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    (fn : Fin source.length) (args : Env source[fn].params) :
    map.eval targetProgram fn args = sourceProgram.eval fn args := by
  funext heap
  unfold SignatureMap.eval
  rw [Program.eval_cast_eq targetProgram (map.toFun fn) (map.signature_eq fn)]
  change ((map.body targetProgram fn).eval targetProgram ⟨args, heap⟩).map _ = _
  rw [embedded fn, Stmt.eval_renameCalls embedded]
  rfl

end Complexity.Language
