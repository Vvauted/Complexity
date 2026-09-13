/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Same-trace cost transport for local nonallocating code

This local fragment excludes allocation, reclaiming scopes and calls, but allows
stores into existing buffers. Its arena readiness supplies the fixed-placement
realization of the same source execution. Existing cost determinism then reuses
fixed-placement cost bounds without imposing additional word-range hypotheses
on the cost contract. No allocator or store is repriced.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Local statements which neither allocate, reclaim nor invoke a callee.
Writes to existing objects and ordinary control flow remain admissible. -/
def NoAllocationOrCalls {signatures : List Signature} {Γ : List Ty} {result : Ty} :
    Complexity.Language.Stmt signatures Γ result → Prop
  | .skip | .assign .. | .ret _ | .write .. => True
  | .letPrim _ body | .read _ _ body | .readNode _ body | .slice _ _ _ body =>
      NoAllocationOrCalls body
  | .alloc .. | .consNode .. | .scope _ | .call .. => False
  | .seq first second => NoAllocationOrCalls first ∧ NoAllocationOrCalls second
  | .ite _ yes no => NoAllocationOrCalls yes ∧ NoAllocationOrCalls no
  | .matchOption _ noneBranch someBranch =>
      NoAllocationOrCalls noneBranch ∧ NoAllocationOrCalls someBranch
  | .while guard body => NoAllocationOrCalls guard ∧ NoAllocationOrCalls body

/-- Readiness for this local fragment realizes the very same source execution;
the existing heap writes and their value-fit premises are retained. -/
theorem ArenaReady.realized_of_noAllocationOrCalls {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish control}
    {w heapLimit depth next₀ next₁ : Nat}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁)
    (localCode : NoAllocationOrCalls stmt) :
    RealizedExec program w depth stmt entry finish control := by
  revert localCode
  induction ready with
  | skip entry => intro _; exact .skip entry
  | assign target value entry fits => intro _; exact .assign target value entry fits
  | letPrim fits _ ih => intro localCode; exact .letPrim fits (ih localCode)
  | @read Γ result kind w heapLimit depth next₀ next₁ buffer index continuation
      entry finish control value loaded body bufferFits indexFits valueFits _ ih =>
      intro localCode
      exact .read bufferFits indexFits loaded valueFits (ih localCode)
  | @readNode Γ result kind w heapLimit depth next₀ next₁ ref continuation
      entry finish control head tail found body valueFits _ ih =>
      intro localCode
      exact .readNode found valueFits (ih localCode)
  | @write Γ result kind w heapLimit depth next buffer index value entry heap
      written bufferFits indexFits valueFits =>
      intro _
      exact .write bufferFits indexFits valueFits written
  | @slice Γ result kind w heapLimit depth next₀ next₁ buffer offset length continuation
      entry finish control view sliced body bufferFits offsetFits lengthFits viewFits _ ih =>
      intro localCode
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih localCode)
  | alloc => exact False.elim
  | consNode => exact False.elim
  | scope => exact False.elim
  | seqNormal _ _ ihHead ihTail =>
      intro localCode
      exact .seqNormal (ihHead localCode.1) (ihTail localCode.2)
  | seqReturn _ ih => intro localCode; exact .seqReturn (ih localCode.1)
  | @iteTrue Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih => intro localCode; exact .iteTrue test (ih localCode.1)
  | @iteFalse Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih => intro localCode; exact .iteFalse test (ih localCode.2)
  | @matchNone Γ result τ w heapLimit depth next₀ next₁ value noneBranch someBranch
      entry finish control selected body _ ih =>
      intro localCode
      exact .matchNone selected (ih localCode.1)
  | @matchSome Γ result τ w heapLimit depth next₀ next₁ value noneBranch someBranch
      entry payload finish control selected body payloadFits _ ih =>
      intro localCode
      exact .matchSome selected payloadFits (ih localCode.2)
  | whileFalse _ ih => intro localCode; exact .whileFalse (ih localCode.1)
  | whileTrue _ _ _ ihGuard ihBody ihRest =>
      intro localCode
      exact .whileTrue (ihGuard localCode.1) (ihBody localCode.2) (ihRest localCode)
  | whileReturn _ _ ihGuard ihBody =>
      intro localCode
      exact .whileReturn (ihGuard localCode.1) (ihBody localCode.2)
  | ret value entry fits => intro _; exact .ret value entry fits
  | callReturn => exact False.elim

/-- Reuse a local nonallocating statement's cost bound for the same actual
arena execution, without assuming the code leaves heap contents unchanged. -/
theorem StmtArenaCostBound.of_noAllocationOrCalls {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry : Complexity.Language.State Γ} {bound : Nat}
    (bounded : StmtCostBound program stmt entry bound)
    (localCode : NoAllocationOrCalls stmt) :
    StmtArenaCostBound program w heapLimit depth stmt entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  let realized := ready.realized_of_noAllocationOrCalls localCode
  obtain ⟨legacySteps, legacyCost⟩ := realized.exists_cost
  have same : legacySteps = steps := (legacyCost.arena heapLimit cursor).deterministic cost
  exact same ▸ bounded realized legacyCost

/-- A nonallocating local function body inherits its fixed-placement bound.
Initialization remains included once; the arena observation supplies all
readiness needed for this conditional cost implication. -/
theorem FunctionArenaCostBound.of_noAllocationOrCalls {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {bound : Env signatures[fn].params → Nat} {w heapLimit depth : Nat}
    (bounded : FunctionCostBound program fn pre (fun args _ => bound args))
    (localCode : NoAllocationOrCalls (program.body fn)) :
    FunctionArenaCostBound program (program.body fn) id pre w heapLimit depth bound := by
  intro args heap allowed finish value execution cursor finalCursor ready steps cost
  let realized := ready.realized_of_noAllocationOrCalls localCode
  obtain ⟨legacySteps, legacyCost⟩ := realized.exists_cost
  have same : legacySteps = steps := (legacyCost.arena heapLimit cursor).deterministic cost
  simpa only [same] using bounded args heap allowed realized legacyCost

end Ram.LanguageCompiler
