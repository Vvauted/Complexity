/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources
import Complexity.Computability.Ram.Compiler.Language.Effects

/-!
# Read-only arena proofs in the fixed-placement interface

The existing `NoHeapWrites` condition excludes allocation, stores and reclaiming
scopes. When it holds for the statement and every actual callee, arena readiness
supplies `RealizedExec` for that same source execution. This is a connection
between existing proof interfaces, not a new execution or effect predicate.

Indexed arena resource contracts can therefore supply ordinary function
realizability, with independent source total correctness supplying termination.
The cost bridge compares the existing observations of the same trace; body
initialization is retained exactly once and no instruction is repriced.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- Read-only arena readiness realizes the same source execution in the
fixed-placement interface. Every actual callee, including recursive calls, is
covered by the program-wide premise; allocating traversals are not admitted. -/
theorem ArenaReady.realized_of_noHeapWrites {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish control}
    {w heapLimit depth next₀ next₁ : Nat}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁)
    (readOnly : NoHeapWrites stmt)
    (callees : ∀ fn, NoHeapWrites (program.body fn)) :
    RealizedExec program w depth stmt entry finish control := by
  revert readOnly
  induction ready with
  | skip entry =>
      intro _
      exact .skip entry
  | assign target value entry fits =>
      intro _
      exact .assign target value entry fits
  | letPrim fits _ ih =>
      intro readOnly
      exact .letPrim fits (ih readOnly)
  | @read Γ result kind w heapLimit depth next₀ next₁ buffer index continuation
      entry finish control value loaded body bufferFits indexFits valueFits _ ih =>
      intro readOnly
      exact .read bufferFits indexFits loaded valueFits (ih readOnly)
  | @readNode Γ result kind w heapLimit depth next₀ next₁ ref continuation
      entry finish control head tail found body valueFits _ ih =>
      intro readOnly
      exact .readNode found valueFits (ih readOnly)
  | write => exact False.elim
  | @slice Γ result kind w heapLimit depth next₀ next₁ buffer offset length continuation
      entry finish control view sliced body bufferFits offsetFits lengthFits viewFits _ ih =>
      intro readOnly
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih readOnly)
  | alloc => exact False.elim
  | consNode => exact False.elim
  | scope => exact False.elim
  | seqNormal _ _ ihHead ihTail =>
      intro readOnly
      exact .seqNormal (ihHead readOnly.1) (ihTail readOnly.2)
  | seqReturn _ ih =>
      intro readOnly
      exact .seqReturn (ih readOnly.1)
  | @iteTrue Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih =>
      intro readOnly
      exact .iteTrue test (ih readOnly.1)
  | @iteFalse Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body _ ih =>
      intro readOnly
      exact .iteFalse test (ih readOnly.2)
  | @matchNone Γ result τ w heapLimit depth next₀ next₁ value noneBranch someBranch
      entry finish control selected body _ ih =>
      intro readOnly
      exact .matchNone selected (ih readOnly.1)
  | @matchSome Γ result τ w heapLimit depth next₀ next₁ value noneBranch someBranch
      entry payload finish control selected body payloadFits _ ih =>
      intro readOnly
      exact .matchSome selected payloadFits (ih readOnly.2)
  | whileFalse _ ih =>
      intro readOnly
      exact .whileFalse (ih readOnly.1)
  | whileTrue _ _ _ ihGuard ihBody ihRest =>
      intro readOnly
      exact .whileTrue (ihGuard readOnly.1) (ihBody readOnly.2) (ihRest readOnly)
  | whileReturn _ _ ihGuard ihBody =>
      intro readOnly
      exact .whileReturn (ihGuard readOnly.1) (ihBody readOnly.2)
  | ret value entry fits =>
      intro _
      exact .ret value entry fits
  | @callReturn Γ result w heapLimit depth next₀ calleeCursor next₁ fn args continuation
      entry calleeFinish value finish control callee body arguments _ _ ihCallee ihBody =>
      intro readOnly
      exact .callReturn arguments (ihCallee (callees fn)) (ihBody readOnly)

/-- Reuse indexed arena resources for an actual read-only function. Source
total correctness supplies the returned execution; the index only describes its
arguments and resource premises, and need not encode a mathematical value uniquely. -/
theorem FunctionRealizable.of_arenaResources {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {arguments : X → Env signatures[fn].params} {pre : X → Heap → Prop}
    {functionPre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {w heapLimit depth : Nat} {reserve : X → Nat}
    (resources : FunctionArenaResources program (program.body fn)
      arguments pre w heapLimit depth reserve)
    (total : FunctionTotal program fn functionPre post)
    (readOnly : ∀ fn, NoHeapWrites (program.body fn))
    (input : ∀ actual heap, functionPre actual heap →
      ∃ x, arguments x = actual ∧ pre x heap ∧ EnvFits w actual ∧ reserve x ≤ heapLimit) :
    FunctionRealizable program w depth fn functionPre := by
  intro actual heap allowed
  obtain ⟨x, rfl, admissible, fits, capacity⟩ := input actual heap allowed
  obtain ⟨finish, value, execution, _⟩ := total (arguments x) heap allowed
  obtain ⟨finalCursor, ready, _⟩ := resources x heap 0 admissible fits
    (by simpa only [Nat.zero_add] using capacity) finish value execution
  exact ⟨finish, value, ready.realized_of_noHeapWrites (readOnly fn) readOnly⟩

/-- Transfer an indexed arena cost bound to the ordinary conditional cost
interface. Cost determinism removes dependence on the chosen width, depth and
readiness witness. This rule supplies neither termination nor realizability of
allocating code: its conclusion is about an already realized source execution. -/
theorem FunctionCostBound.of_arenaCostBound {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {arguments : X → Env signatures[fn].params} {pre : X → Heap → Prop}
    {functionPre : Env signatures[fn].params → Heap → Prop}
    {functionBound : Env signatures[fn].params → Heap → Nat}
    {w heapLimit depth : Nat} {reserve bound : X → Nat}
    (resources : FunctionArenaResources program (program.body fn)
      arguments pre w heapLimit depth reserve)
    (bounded : FunctionArenaCostBound program (program.body fn)
      arguments pre w heapLimit depth bound)
    (input : ∀ actual heap, functionPre actual heap →
      ∃ x, arguments x = actual ∧ pre x heap ∧ EnvFits w actual ∧
        reserve x ≤ heapLimit ∧ bound x ≤ functionBound actual heap) :
    FunctionCostBound program fn functionPre functionBound := by
  intro actual heap allowed actualWidth actualDepth finish value execution steps cost
  obtain ⟨x, rfl, admissible, fits, capacity, budget⟩ := input actual heap allowed
  obtain ⟨finalCursor, ready, _⟩ := resources x heap 0 admissible fits
    (by simpa only [Nat.zero_add] using capacity) finish value execution.erase
  obtain ⟨arenaSteps, arenaCost⟩ := ready.exists_cost
  have sameSteps : steps = arenaSteps := (cost.arena heapLimit 0).deterministic arenaCost
  have observedBound := bounded x heap admissible finish value execution.erase ready arenaCost
  simpa only [sameSteps] using observedBound.trans budget

end Ram.LanguageCompiler
