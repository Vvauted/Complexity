/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call

/-!
# Arena cost bounds across standalone calls

A standalone source call restores caller locals and retains the callee's actual
final heap. Its existing source postcondition connects that heap to the next
statement's cost certificate. The rule below uses the existing call and normal
sequence charges, including callee initialization exactly once.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

universe u

/-- Compose an indexed callee bound and its independent source contract with
the next statement at the actual final heap. The empty call continuation cannot
return from the caller, so no early-return sequence envelope is needed. -/
theorem call_seq_at_of_spec {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {entry : Complexity.Language.State Γ}
    {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {second : Complexity.Language.Stmt signatures Γ result}
    {calleeArgs : X → Env signatures[fn].params} {costPre : X → Heap → Prop}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : X → Nat} {nextBound : Nat}
    (callee : FunctionArenaCostBound program (program.body fn) calleeArgs costPre
      w heapLimit depth calleeBound)
    (specification : FunctionTotal program fn pre post)
    (index : X) (arguments_eq : calleeArgs index = args.eval entry.locals)
    (costInput : costPre index entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtArenaCostBound program w heapLimit (depth + 1) second
        ⟨entry.locals, heap⟩ nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (.seq (.call fn args .skip) second) entry
      (callCost program fn (calleeBound index) + 2 + nextBound) := by
  intro finish control execution cursor finalCursor ready steps cost
  have bounded := callee index entry.heap costInput
  rw [arguments_eq] at bounded
  cases cost with
  | @seqNormal Γ result depth next₀ middleCursor next₁ first second entry middle
      finish control firstExec secondExec firstReady secondReady firstSteps secondSteps
      firstCost secondCost =>
      cases firstCost with
      | @callReturn Γ result depth next₀ calleeCursor next₁ fn args continuation entry
          calleeFinish value finish control arguments calleeExec bodyExec calleeReady
          bodyReady calleeSteps bodySteps calleeCost bodyCost =>
          cases bodyCost
          have property := specification.postcondition (args := args.eval entry.locals)
            (heap := entry.heap) input calleeExec
          have calleeLe := callCost_mono program fn (bounded _ _ _ _ calleeCost)
          have tailLe := body value calleeFinish.heap property _ _ secondCost
          simpa only [Nat.add_zero] using
            Nat.add_le_add (Nat.add_le_add_right calleeLe 2) tailLe
  | seqReturn firstCost =>
      cases firstCost with
      | callReturn calleeCost bodyCost => cases bodyCost

end Ram.LanguageCompiler.StmtArenaCostBound
