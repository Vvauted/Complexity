/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Input-dependent arena call bounds

An index in an existing function cost contract may retain mathematical data and
its actual source representation. The caller proves the argument equality and
the contract's precondition at the actual entry heap. These rules compose that
input-dependent bound with the real continuation, without choosing another
execution or requiring a constant bound for all inputs of the callee.

The selected bound already includes callee initialization; only the existing
call-frame overhead is added. Imported calls retain their actual program entry.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

universe u

variable {X : Type u} {signatures : List Signature}
variable {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
variable {Γ : List Ty} {result : Ty} {entry : Complexity.Language.State Γ}

/-- Select an input-dependent cost certificate using its actual arguments.
The continuation receives the actual returned value and heap at the caller's
depth. Word ranges and termination remain separate from this cost implication. -/
theorem call_at {fn : Fin signatures.length}
    {calleeArgs : X → Env signatures[fn].params} {pre : X → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound program (program.body fn) calleeArgs pre
      w heapLimit depth calleeBound)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (allowed : pre index entry.heap)
    (body : ∀ value heap, StmtArenaCostBound program w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1) (.call fn args continuation) entry
      (callCost program fn (calleeBound index) + nextBound) := by
  intro finish control execution cursor finalCursor ready steps cost
  have bounded := callee index entry.heap allowed
  rw [arguments_eq] at bounded
  cases cost with
  | callReturn calleeCost bodyCost =>
      exact Nat.add_le_add (callCost_mono program fn (bounded _ _ _ _ calleeCost))
        (body _ _ _ _ bodyCost)

/-- Transport an indexed bound across the actual callee signature equality. -/
theorem call_at_of_eq {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {calleeArgs : X → Env signature.params} {pre : X → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    (callee : FunctionArenaCostBound program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs pre w heapLimit depth calleeBound)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (allowed : pre index entry.heap)
    (body : ∀ value heap, StmtArenaCostBound program w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) entry
      (callCost program fn (calleeBound index) + nextBound) := by
  cases same
  exact call_at callee index arguments_eq allowed body

/-- Use an indexed certificate from an imported program. Neither relocation nor
the mathematical index reprices the actual call or changes its entry heap. -/
theorem call_at_imported {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {calleeArgs : X → Env source[fn].params} {pre : X → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat}
    {args : Args Γ source[fn].params}
    {continuation : Complexity.Language.Stmt target (source[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound sourceProgram (sourceProgram.body fn) calleeArgs pre
      w heapLimit depth calleeBound)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (allowed : pre index entry.heap)
    (body : ∀ value heap, StmtArenaCostBound targetProgram w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn) (map.signature_eq fn) args continuation)
      entry (callCost targetProgram (map.toFun fn) (calleeBound index) + nextBound) := by
  refine call_at_of_eq (args := args) (entry := entry) (calleeBound := calleeBound)
    (nextBound := nextBound) (map.signature_eq fn) ?_ index arguments_eq allowed body
  have relocated := callee.renameCalls embedded
  rw [← embedded fn] at relocated
  exact relocated

end Ram.LanguageCompiler.StmtArenaCostBound
