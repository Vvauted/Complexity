/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Tactic.Ram.Total

/-!
# Array-store verification conditions

`ram_total_store represented at index := stored [facts]` applies the existing
array-store contract to the actual leading store, opening at most one sequence.
The representation supplies the array's base, logical contents and heap bound;
the address and value expressions are inferred from the current statement.
The author chooses the mathematical index and stored word.

The named obligations are `indexBound`, `representation`, `addressReads`,
`valueReads`, `addressValue`, `storedValue` and `continuation`. Only complete
solutions of the first six are tried. The continuation receives the actual
state update, `List.set` representation and array-external frame, without
simplifying its specification or executing the next statement.

The supplied representation need not concern the identical source state:
`ArrayAt` observes only memory, so local-register updates are definitionally
irrelevant. A genuine heap change leaves a representation obligation unless
the available facts establish it. No instruction budget enters the proof.
-/

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

/-- Apply the represented-array store rule to the current statement, retaining
unresolved safety and mathematical conditions and the untouched continuation. -/
syntax (name := ramTotalStore) "ram_total_store " term:max
  " at " term:max " := " term:max (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_total_store $represented at $index := $stored) =>
      `(tactic| ram_total_store $represented at $index := $stored [])

elab_rules : tactic
  | `(tactic| ram_total_store $represented at $index := $stored [$facts,*]) =>
      focus <| withMainContext do
        let proof ← elabTerm represented none
        let proofType ← instantiateMVars (← inferType proof)
        let some arrayType ← whnfUntil proofType ``Ram.Source.ArrayAt |
          throwErrorAt represented "Expected an ArrayAt proof, got {proofType}"
        unless arrayType.isAppOfArity ``Ram.Source.ArrayAt 5 do
          throwErrorAt represented "Expected a fully applied ArrayAt proof, got {arrayType}"
        let parameters := arrayType.getAppArgs
        let width ← Term.exprToSyntax parameters[0]!
        let heapLimit ← Term.exprToSyntax parameters[1]!
        let base ← Term.exprToSyntax parameters[2]!
        let contents ← Term.exprToSyntax parameters[3]!
        let representedProof ← Term.exprToSyntax proof
        let applyStore ← `(tactic|
          refine Ram.Source.Verification.TotalWP.of_relContract
            ((Ram.Source.Array.store_contract (w := $width) (control := 0)
              (heapLimit := $heapLimit) (base := $base) (xs := $contents)
              (i := $index) ?indexBound _ _ $stored).total) ?pre ?continuation)
        evalTactic (← `(tactic|
          first
          | $applyStore:tactic
          | (rw [Ram.Source.Verification.TotalWP.seq_iff]
             $applyStore:tactic)))
        for goal in ← getUnsolvedGoals do
          goal.setTag (← goal.getTag).eraseMacroScopes
        evalTactic (← `(tactic|
          case' pre =>
            refine ⟨?representation, ?addressReads, ?valueReads, ?addressValue, ?storedValue⟩))
        for goal in ← getUnsolvedGoals do
          goal.setTag (← goal.getTag).eraseMacroScopes
        evalTactic (← `(tactic|
          case' representation =>
            try (solve | exact $representedProof | (ram_simp [$facts,*] <;> assumption))))
        evalTactic (← `(tactic|
          case' indexBound | addressReads | valueReads | addressValue | storedValue =>
            try (solve | (ram_simp [$facts,*] <;> assumption))))
