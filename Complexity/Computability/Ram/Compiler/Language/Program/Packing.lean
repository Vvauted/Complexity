/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Packing
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Call
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call

/-!
# RAM resources for executable program-entry packing

Structural packing is real source code. Its field copies use `primCodeSize`,
its invocation uses `callCost`, and returning copies the actual result fields.
The measured bridge retains the original callee's actual heap, result, cursor
and count through the checked source-table embedding. Entering that callee
requires one additional call level; forming products does not allocate a heap
object or reset the arena cursor.

Readiness and measured execution remain separate from upper bounds. The cost
rule applies an existing indexed callee certificate to the same execution and
does not manufacture termination from a budget. These bridges neither change
the fixed `Program.Input`/`RamInput` layout nor install a host-side conversion.
-/

namespace Complexity.Program.Packing

open Language Ram.LanguageCompiler

/-- The compiler's actual product-construction work, excluding the final call
and return. This is derived from the existing primitive lowering. -/
@[simp] def cost : {Γ : List Ty} → {τ : Ty} → Packing Γ τ → Nat
  | _, _, .done _ => 0
  | _, _, .pair left right rest => primCodeSize (.pair left right) + rest.cost

/-- The complete packing-call core budget from an existing callee body budget.
The actual selected signature supplies the result-copy width. This includes
structural assembly and the return, but not the enclosing function's own
initialization or outer invocation. -/
def callBound {Γ : List Ty} {τ : Ty} (packing : Packing Γ τ)
    {signatures : List Signature} (program : Language.Program signatures)
    (fn : Fin signatures.length) (calleeBodyBound : Nat) : Nat :=
  packing.cost + callCost program fn calleeBodyBound +
    (2 * fieldCount signatures[fn].result + 2)

/-- Packing and the selected call add a fixed compiler-derived constant to the
callee body budget. The zero-budget value here measures overhead algebraically;
it does not claim that the callee can actually execute in zero instructions. -/
theorem callBound_eq {Γ : List Ty} {τ : Ty} (packing : Packing Γ τ)
    {signatures : List Signature} (program : Language.Program signatures)
    (fn : Fin signatures.length) (calleeBodyBound : Nat) :
    packing.callBound program fn calleeBodyBound =
      calleeBodyBound + packing.callBound program fn 0 := by
  simp only [callBound, callCost, Ram.LocalCompiler.Function.callSteps_eq]
  omega

/-- Observe the named budget at a proved complete callee signature. Only the
type of the actual returned fields is transported; no work is added or removed. -/
theorem callBound_of_signature {Γ : List Ty} {τ : Ty} (packing : Packing Γ τ)
    {signatures : List Signature} (program : Language.Program signatures)
    (fn : Fin signatures.length) {selected : Signature} (same : signatures[fn] = selected)
    (calleeBodyBound : Nat) :
    packing.callBound program fn calleeBodyBound =
      packing.cost + callCost program fn calleeBodyBound +
        (2 * fieldCount selected.result + 2) := by
  simp only [callBound, same]

/-- Finite-word conditions for the actual atoms selected and pairs assembled.
There is no arithmetic operation, heap access or additional capacity premise. -/
@[simp] def Fits (w : Nat) : {Γ : List Ty} → {τ : Ty} → Packing Γ τ → Env Γ → Prop
  | _, _, .done value, args => ValueFits w (value.eval args)
  | _, _, .pair left right rest, args =>
      PrimFits w args (.pair left right) ∧
        rest.Fits w (Env.cons (left.eval args, right.eval args) args)

/-- All assembled fields fit when every actual packing step does. -/
theorem Fits.eval_fits {w : Nat} {Γ : List Ty} {τ : Ty} {packing : Packing Γ τ}
    {args : Env Γ} (fits : packing.Fits w args) : ValueFits w (packing.eval args) := by
  induction packing with
  | done _ => exact fits
  | pair _ _ _ ih => exact ih fits.2

/-- An imported measured callee supplies the actual execution of the packing
call. Its result and final heap/cursor are unchanged; only actual product copies,
callee initialization, call-frame work and result return are added to its count. -/
theorem call_measured_imported
    {source target : List Signature}
    {sourceProgram : Language.Program source} {targetProgram : Language.Program target}
    {map : SignatureMap source target} (embedded : sourceProgram.Embeds map targetProgram)
    {τ result : Ty} (fn : Fin source.length) (same : source[fn] = ⟨[τ], result⟩)
    {w heapLimit depth cursor : Nat} {Γ : List Ty} (packing : Packing Γ τ)
    (entry : Language.State Γ) (fits : packing.Fits w entry.locals)
    {P : Heap → Value result → Nat → Nat → Prop}
    (callee : ArenaMeasured sourceProgram w heapLimit depth
      (cast (congrArg (fun s => Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn))
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧ P finish.heap value finalCursor steps)
      ⟨Env.cons (packing.eval entry.locals) Env.empty, entry.heap⟩ cursor) :
    ArenaMeasured targetProgram w heapLimit (depth + 1)
      (packing.call (map.toFun fn) ((map.signature_eq fn).trans same))
      (fun finish control finalCursor steps => ∃ value calleeSteps,
        control = .returned value ∧ P finish.heap value finalCursor calleeSteps ∧
          steps = packing.cost + callCost targetProgram (map.toFun fn) (calleeSteps + 2) +
            (2 * fieldCount result + 2)) entry cursor := by
  induction packing with
  | done atom =>
      apply ArenaMeasured.call_measured_imported embedded same
        (args := .cons atom .nil) (continuation := .ret (.var .here)) (entry := entry)
        (EnvFits.cons (EnvFits.empty w) _ fits) callee
      intro finish value finalCursor steps property valueFits
      apply ArenaMeasured.ret valueFits
      exact ⟨value, steps, rfl, property, by simp⟩
  | @pair Γ leftType rightType τ left right rest ih =>
      apply ArenaMeasured.letPrim fits.1
      have measured := ih same
        (Language.State.cons (τ := .prod leftType rightType)
          (left.eval entry.locals, right.eval entry.locals) entry) fits.2 callee
      apply measured.mono_post
      rintro finish control finalCursor steps ⟨value, calleeSteps, returned, property, counted⟩
      exact ⟨value, calleeSteps, returned, property, by
        simp only [cost, counted, Nat.add_assoc]⟩

/-- Bound the actual packing call using an indexed bound for the selected
callee. Termination, word ranges and available storage are separate obligations.
The bound includes all product copies and the actual final return. -/
theorem call_costBound {X : Type*} {signatures : List Signature}
    {program : Language.Program signatures} {τ result : Ty}
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩)
    {w heapLimit depth : Nat} {calleeArgs : X → Env [τ]}
    {pre : X → Heap → Prop} {bound : X → Nat}
    (callee : FunctionArenaCostBound program
      (cast (congrArg (fun s => Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs pre w heapLimit depth bound)
    {Γ : List Ty} (packing : Packing Γ τ) (entry : Language.State Γ) (x : X)
    (arguments : calleeArgs x = Env.cons (packing.eval entry.locals) Env.empty)
    (allowed : pre x entry.heap) :
    StmtArenaCostBound program w heapLimit (depth + 1) (packing.call fn same) entry
      (packing.cost + callCost program fn (bound x) + (2 * fieldCount result + 2)) := by
  induction packing with
  | done atom =>
      intro finish control execution cursor finalCursor ready steps counted
      simpa only [cost, Nat.zero_add] using
        (StmtArenaCostBound.call_at_of_eq (args := .cons atom .nil)
          (continuation := .ret (.var .here)) (entry := entry) same callee x arguments allowed
          (fun _ _ => StmtArenaCostBound.ret (.var .here) _)) execution ready counted
  | @pair Γ leftType rightType τ left right rest ih =>
      intro finish control execution cursor finalCursor ready steps counted
      simpa only [cost, Nat.add_assoc] using
        (StmtArenaCostBound.letPrim (.pair left right)
          (ih same callee
            (Language.State.cons (τ := .prod leftType rightType)
              (left.eval entry.locals, right.eval entry.locals) entry) arguments allowed))
          execution ready counted

private theorem program_body_eq_call {signatures : List Signature} {Γ : List Ty}
    {τ result : Ty} (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩) :
    (packing.program source fn same).body (entry Γ result signatures) =
      packing.call ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn)
        (((SignatureMap.appendRight [signature Γ result] signatures).signature_eq fn).trans
          same) := by
  simpa only [SignatureMap.body, SignatureMap.appendLeft, bodies, cast_eq] using
    packing.body_entry source fn same

/-- Measure the actual newly added entry using the original callee's measured
execution. The preloaded argument layout remains unchanged, and one call level
is added independently of the number of fields or the input size. -/
theorem program_measured {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩)
    {w heapLimit depth cursor : Nat} (args : Env Γ) (heap : Heap)
    (fits : packing.Fits w args) {P : Heap → Value result → Nat → Nat → Prop}
    (callee : ArenaMeasured source w heapLimit depth
      (cast (congrArg (fun s => Language.Stmt signatures s.params s.result) same)
        (source.body fn))
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧ P finish.heap value finalCursor steps)
      ⟨Env.cons (packing.eval args) Env.empty, heap⟩ cursor) :
    ArenaMeasured (packing.program source fn same) w heapLimit (depth + 1)
      ((packing.program source fn same).body (entry Γ result signatures))
      (fun finish control finalCursor steps => ∃ value calleeSteps,
        control = .returned value ∧ P finish.heap value finalCursor calleeSteps ∧
          steps = packing.cost +
            callCost (packing.program source fn same)
              ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn)
              (calleeSteps + 2) + (2 * fieldCount result + 2)) ⟨args, heap⟩ cursor := by
  have measured := packing.call_measured_imported
    (source.embeds_extend [signature Γ result] (packing.bodies fn same))
    fn same ⟨args, heap⟩ fits callee
  rw [program_body_eq_call]
  exact measured

/-- Bound every actual control outcome of the added entry's source body. The
callee certificate includes its own initialization, while this core bound adds
the real packing, call and return work. The new function's initialization and
outer invocation remain the responsibility of the shared execution interface. -/
theorem program_stmt_costBound {X : Type*} {signatures : List Signature} {Γ : List Ty}
    {τ result : Ty} (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩)
    {w heapLimit depth : Nat} {args : X → Env Γ} {pre : X → Heap → Prop}
    {bound : X → Nat}
    (callee : FunctionArenaCostBound source
      (cast (congrArg (fun s => Language.Stmt signatures s.params s.result) same)
        (source.body fn))
      (fun x => Env.cons (packing.eval (args x)) Env.empty) pre w heapLimit depth bound)
    (x : X) (heap : Heap) (allowed : pre x heap) :
    StmtArenaCostBound (packing.program source fn same) w heapLimit (depth + 1)
      ((packing.program source fn same).body (entry Γ result signatures)) ⟨args x, heap⟩
      (packing.cost +
        callCost (packing.program source fn same)
          ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn) (bound x) +
        (2 * fieldCount result + 2)) := by
  have embedded := source.embeds_extend [signature Γ result] (packing.bodies fn same)
  have relocated := callee.renameCalls embedded
  have linked : FunctionArenaCostBound (packing.program source fn same)
      (cast (congrArg (fun s =>
        Language.Stmt ([signature Γ result] ++ signatures) s.params s.result)
          (((SignatureMap.appendRight [signature Γ result] signatures).signature_eq fn).trans
            same))
        ((packing.program source fn same).body
          ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn)))
      (fun x => Env.cons (packing.eval (args x)) Env.empty) pre w heapLimit depth bound := by
    rw [Language.Stmt.renameCalls_cast
      (SignatureMap.appendRight [signature Γ result] signatures) same, ← embedded fn]
      at relocated
    simpa only [SignatureMap.body, cast_cast] using relocated
  rw [program_body_eq_call]
  intro finish control execution cursor finalCursor ready steps counted
  exact packing.call_costBound
    ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn)
    (((SignatureMap.appendRight [signature Γ result] signatures).signature_eq fn).trans same)
    linked ⟨args x, heap⟩ x rfl allowed execution ready counted

/-- The added function inherits the same core budget with its two actual
initialization instructions. This is the function-contract form of
`program_stmt_costBound`, not a second cost or relocation proof. -/
theorem program_costBound {X : Type*} {signatures : List Signature} {Γ : List Ty}
    {τ result : Ty} (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩)
    {w heapLimit depth : Nat} {args : X → Env Γ} {pre : X → Heap → Prop}
    {bound : X → Nat}
    (callee : FunctionArenaCostBound source
      (cast (congrArg (fun s => Language.Stmt signatures s.params s.result) same)
        (source.body fn))
      (fun x => Env.cons (packing.eval (args x)) Env.empty) pre w heapLimit depth bound) :
    FunctionArenaCostBound (packing.program source fn same)
      ((packing.program source fn same).body (entry Γ result signatures)) args pre
      w heapLimit (depth + 1)
      (fun x => packing.cost +
        callCost (packing.program source fn same)
          ((SignatureMap.appendRight [signature Γ result] signatures).toFun fn) (bound x) +
        (2 * fieldCount result + 2) + 2) := by
  intro x heap allowed finish value execution cursor finalCursor ready steps counted
  exact Nat.add_le_add_right
    (packing.program_stmt_costBound source fn same callee x heap allowed
      execution ready counted) 2

end Complexity.Program.Packing
