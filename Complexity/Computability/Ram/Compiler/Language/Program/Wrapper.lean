/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Call
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call

/-!
# Composing actual source wrapper bodies

These rules expose a real callee body as a proof obligation while retaining its
call boundary. They support arbitrary typed parameters and results, not a fixed
record layout or operation. The caller executes the same body at one additional
call level, with its initialization and call/return work charged by the existing
compiler. Neither rule inlines code at runtime or installs a host operation.

The measured rule carries the actual callee's final heap and cursor directly
into its continuation. The independent cost rule applies to every actual
control outcome and does not infer termination from a numerical envelope.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Verify an actual callee body before continuing at its actual result, heap
and cursor. The continuation is a postcondition of that same measured body;
the ordinary call rule supplies the returned-value range. -/
theorem ArenaMeasured.call_body {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth cursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (arguments : EnvFits w (args.eval entry.locals))
    (callee : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor steps => ∃ value, control = .returned value ∧
        (ValueFits w value → ArenaMeasured program w heapLimit (depth + 1) continuation
          (fun final outcome cursor tailSteps =>
            post final.tail outcome cursor (callCost program fn (steps + 2) + tailSteps))
          (Complexity.Language.State.cons value (entry.restore finish)) finalCursor))
      (entry.enter (args.eval entry.locals)) cursor) :
    ArenaMeasured program w heapLimit (depth + 1) (.call fn args continuation)
      post entry cursor := by
  apply ArenaMeasured.call_measured rfl arguments callee
  intro finish value finalCursor steps body fits
  exact body fits

/-- A pointwise bound on the real callee body composes with the actual call and
continuation. Callee initialization is added once; the enclosing function's
initialization and outer invocation remain outside this statement-core bound. -/
theorem StmtArenaCostBound.call_body {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {entry : Complexity.Language.State Γ} {calleeBound nextBound : Nat}
    (callee : StmtArenaCostBound program w heapLimit depth (program.body fn)
      (entry.enter (args.eval entry.locals)) calleeBound)
    (body : ∀ value heap, StmtArenaCostBound program w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1) (.call fn args continuation) entry
      (callCost program fn (calleeBound + 2) + nextBound) := by
  intro finish control execution cursor finalCursor ready steps counted
  cases counted with
  | callReturn calleeCost tailCost =>
      exact Nat.add_le_add
        (callCost_mono program fn (Nat.add_le_add_right (callee _ _ calleeCost) 2))
        (body _ _ _ _ tailCost)

end Ram.LanguageCompiler
