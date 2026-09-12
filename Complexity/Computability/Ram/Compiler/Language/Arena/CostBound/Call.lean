/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound
import Complexity.Language.Linking.Verification

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

/-- Compose an indexed cost bound with an existing source specification.
The continuation and final comparison may depend on the actual returned value
and final heap. The postcondition concerns that same supplied execution; no
resource witness or new termination argument is constructed. -/
theorem call_at_of_spec_le {fn : Fin signatures.length}
    {calleeArgs : X → Env signatures[fn].params} {costPre : X → Heap → Prop}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Value signatures[fn].result → Heap → Nat}
    {bound : Nat} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound program (program.body fn) calleeArgs costPre
      w heapLimit depth calleeBound)
    (specification : FunctionTotal program fn pre post)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (nextCost : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound program w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      callCost program fn (calleeBound index) + nextBound value heap ≤ bound) :
    StmtArenaCostBound program w heapLimit (depth + 1) (.call fn args continuation)
      entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  have bounded := callee index entry.heap costInput
  rw [arguments_eq] at bounded
  cases cost with
  | @callReturn Γ result depth next₀ calleeCursor next₁ fn args continuation entry
      calleeFinish value finish control arguments calleeExec bodyExec calleeReady bodyReady
      calleeSteps bodySteps calleeCost bodyCost =>
      have property := specification.postcondition (args := args.eval entry.locals)
        (heap := entry.heap) input calleeExec
      have calleeLe := bounded _ _ calleeExec calleeReady calleeCost
      have bodyLe := nextCost value calleeFinish.heap property bodyExec bodyReady bodyCost
      exact (Nat.add_le_add (callCost_mono program fn calleeLe) bodyLe).trans
        (combine value calleeFinish.heap property)

/-- Infer a bound uniform over this call's possible outcomes while retaining
the supplied specification in its continuation. The bound may still depend on
the chosen mathematical input; neither the value nor the final heap is fixed. -/
theorem call_at_of_spec {fn : Fin signatures.length}
    {calleeArgs : X → Env signatures[fn].params} {costPre : X → Heap → Prop}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound program (program.body fn) calleeArgs costPre
      w heapLimit depth calleeBound)
    (specification : FunctionTotal program fn pre post)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound program w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1) (.call fn args continuation) entry
      (callCost program fn (calleeBound index) + nextBound) :=
  call_at_of_spec_le (nextBound := fun _ _ => nextBound)
    callee specification index arguments_eq costInput input body (fun _ _ _ => Nat.le_refl _)

/-- Transport the same specification and dependent continuation bound across
the callee's complete signature equality. -/
theorem call_at_of_spec_le_of_eq {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {calleeArgs : X → Env signature.params} {costPre : X → Heap → Prop}
    {pre : Env signature.params → Heap → Prop}
    {post : Env signature.params → Heap → Value signature.result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Value signature.result → Heap → Nat}
    {bound : Nat} {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    (callee : FunctionArenaCostBound program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs costPre w heapLimit depth calleeBound)
    (specification : FunctionTotal program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s => Env s.params → Heap → Value s.result → Heap → Prop)
        same.symm) post))
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (nextCost : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound program w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      callCost program fn (calleeBound index) + nextBound value heap ≤ bound) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) entry bound := by
  cases same
  exact call_at_of_spec_le callee specification index arguments_eq costInput input nextCost combine

/-- The fixed continuation envelope also respects a proved callee signature,
without dropping the actual source postcondition. -/
theorem call_at_of_spec_of_eq {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {calleeArgs : X → Env signature.params} {costPre : X → Heap → Prop}
    {pre : Env signature.params → Heap → Prop}
    {post : Env signature.params → Heap → Value signature.result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat} {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    (callee : FunctionArenaCostBound program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs costPre w heapLimit depth calleeBound)
    (specification : FunctionTotal program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s => Env s.params → Heap → Value s.result → Heap → Prop)
        same.symm) post))
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound program w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) entry
      (callCost program fn (calleeBound index) + nextBound) := by
  cases same
  exact call_at_of_spec callee specification index arguments_eq costInput input body

/-- Relocate an indexed cost certificate and its independent source
specification together. Both the dependent continuation and the comparison
receive the original contract at the actual linked call's final heap. -/
theorem call_at_of_spec_le_imported {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {calleeArgs : X → Env source[fn].params} {costPre : X → Heap → Prop}
    {pre : Env source[fn].params → Heap → Prop}
    {post : Env source[fn].params → Heap → Value source[fn].result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Value source[fn].result → Heap → Nat}
    {bound : Nat} {args : Args Γ source[fn].params}
    {continuation : Complexity.Language.Stmt target (source[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound sourceProgram (sourceProgram.body fn) calleeArgs costPre
      w heapLimit depth calleeBound)
    (specification : FunctionTotal sourceProgram fn pre post)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (nextCost : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound targetProgram w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      callCost targetProgram (map.toFun fn) (calleeBound index) + nextBound value heap ≤ bound) :
    StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn) (map.signature_eq fn) args continuation)
      entry bound := by
  refine call_at_of_spec_le_of_eq (args := args) (entry := entry)
    (calleeBound := calleeBound) (nextBound := nextBound) (bound := bound)
    (map.signature_eq fn) ?_ (FunctionTotal.renameCalls embedded specification)
    index arguments_eq costInput input nextCost combine
  have relocated := callee.renameCalls embedded
  rw [← embedded fn] at relocated
  exact relocated

/-- Imported calls can infer a fixed continuation envelope while retaining
their original source contract on the actual returned value and heap. -/
theorem call_at_of_spec_imported {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {calleeArgs : X → Env source[fn].params} {costPre : X → Heap → Prop}
    {pre : Env source[fn].params → Heap → Prop}
    {post : Env source[fn].params → Heap → Value source[fn].result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat} {args : Args Γ source[fn].params}
    {continuation : Complexity.Language.Stmt target (source[fn].result :: Γ) result}
    (callee : FunctionArenaCostBound sourceProgram (sourceProgram.body fn) calleeArgs costPre
      w heapLimit depth calleeBound)
    (specification : FunctionTotal sourceProgram fn pre post)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound targetProgram w heapLimit (depth + 1) continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn) (map.signature_eq fn) args continuation)
      entry (callCost targetProgram (map.toFun fn) (calleeBound index) + nextBound) :=
  call_at_of_spec_le_imported (nextBound := fun _ _ => nextBound)
    embedded callee specification index arguments_eq costInput input body
    (fun _ _ _ => Nat.le_refl _)

end Ram.LanguageCompiler.StmtArenaCostBound
