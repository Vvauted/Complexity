/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization.ReadOnly
import Complexity.Computability.Ram.Compiler.Language.CostBound

/-!
# Structural bounds for actual arena executions

`StmtArenaCostBound` bounds the existing `ArenaExecutionCost` of the same source
execution and readiness witness. It does not supply termination, choose an arena
cursor or reinterpret instructions. Normal completion and early return are both
covered, and sequential continuations retain the actual intermediate state.

Uniform callee contracts reuse `FunctionArenaCostBound`, including allocating
functions. They include body initialization once; the call rule supplies only
the enclosing call charge. Imported contracts retain their actual source bodies.
The read-only bridge reuses legacy bounds only under the existing no-write
conditions, never as a substitute for an allocating execution's cost proof.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- Bound every actual cost observation of this statement at this entry.
Cursor endpoints remain those of the supplied readiness, not budget choices. -/
def StmtArenaCostBound {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w heapLimit depth : Nat)
    {Γ : List Ty} {result : Ty} (stmt : Complexity.Language.Stmt signatures Γ result)
    (entry : Complexity.Language.State Γ) (bound : Nat) : Prop :=
  ∀ {finish control} (execution : Complexity.Language.Exec program stmt entry finish control)
    {cursor finalCursor} (ready : ArenaReady execution w heapLimit depth cursor finalCursor)
    {steps}, ArenaExecutionCost ready steps → steps ≤ bound

namespace StmtArenaCostBound

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry : Complexity.Language.State Γ} {bound bound' : Nat}

/-- Weaken the bound without changing the observed execution. -/
theorem mono (bounded : StmtArenaCostBound program w heapLimit depth stmt entry bound)
    (budget : bound ≤ bound') :
    StmtArenaCostBound program w heapLimit depth stmt entry bound' := by
  intro finish control execution cursor finalCursor ready steps cost
  exact (bounded execution ready cost).trans budget

/-- Empty statements have zero core instructions. -/
theorem skip (entry : Complexity.Language.State Γ) :
    StmtArenaCostBound program w heapLimit depth
      (.skip : Complexity.Language.Stmt signatures Γ result) entry 0 := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost
  exact Nat.le_refl _

/-- Assignment retains the primitive's existing field-copy count. -/
theorem assign {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ)
    (entry : Complexity.Language.State Γ) :
    StmtArenaCostBound program w heapLimit depth
      (.assign target value : Complexity.Language.Stmt signatures Γ result)
      entry (primCodeSize value) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost
  exact Nat.le_refl _

/-- Return copies the actual result fields and sets the existing return flags. -/
theorem ret (value : Atom Γ result) (entry : Complexity.Language.State Γ) :
    StmtArenaCostBound program w heapLimit depth (.ret value) entry
      (2 * fieldCount result + 2) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost
  exact Nat.le_refl _

/-- A primitive binding passes its real value into the continuation. -/
theorem letPrim {τ : Ty} (value : Prim Γ τ)
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (body : StmtArenaCostBound program w heapLimit depth continuation
      (Complexity.Language.State.cons (value.eval entry.locals) entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.letPrim value continuation) entry
      (primCodeSize value + bound) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | letPrim tail => exact Nat.add_le_add_left (body _ _ tail) _

/-- Normal completion resumes at the actual intermediate state and cursor.
The maximum also covers early return, which skips the continuation entirely. -/
theorem seq {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound secondBound : Nat}
    (head : StmtArenaCostBound program w heapLimit depth first entry firstBound)
    (tail : ∀ middle,
      StmtArenaCostBound program w heapLimit depth second middle secondBound) :
    StmtArenaCostBound program w heapLimit depth (.seq first second) entry
      (firstBound + max (2 + secondBound) 3) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | seqNormal firstCost secondCost =>
      have bounded := Nat.add_le_add (Nat.add_le_add_right (head _ _ firstCost) 2)
        (tail _ _ _ secondCost)
      calc
        _ ≤ firstBound + (2 + secondBound) := by
          simpa only [Nat.add_assoc] using bounded
        _ ≤ firstBound + max (2 + secondBound) 3 :=
          Nat.add_le_add_left (Nat.le_max_left (2 + secondBound) 3) firstBound
  | seqReturn firstCost =>
      exact (Nat.add_le_add_right (head _ _ firstCost) 3).trans
        (Nat.add_le_add_left (Nat.le_max_right (2 + secondBound) 3) firstBound)

/-- Each Boolean branch retains its selection equation and its own count.
The maximum is a uniform bound, not a charge for executing both branches. -/
theorem ite {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesCost : condition.eval entry.locals = true →
      StmtArenaCostBound program w heapLimit depth yes entry yesBound)
    (noCost : condition.eval entry.locals = false →
      StmtArenaCostBound program w heapLimit depth no entry noBound) :
    StmtArenaCostBound program w heapLimit depth (.ite condition yes no) entry
      (max (yesBound + 3) (noBound + 2)) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | iteTrue branch =>
      exact (Nat.add_le_add_right (yesCost (by assumption) _ _ branch) 3).trans
        (Nat.le_max_left _ _)
  | iteFalse branch =>
      exact (Nat.add_le_add_right (noCost (by assumption) _ _ branch) 2).trans
        (Nat.le_max_right _ _)

/-- Uniform branch bounds need no mathematical guard contract. -/
theorem ite_max {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesCost : StmtArenaCostBound program w heapLimit depth yes entry yesBound)
    (noCost : StmtArenaCostBound program w heapLimit depth no entry noBound) :
    StmtArenaCostBound program w heapLimit depth (.ite condition yes no) entry
      (max (yesBound + 3) (noBound + 2)) :=
  ite (fun _ => yesCost) (fun _ => noCost)

/-- Optional payload copying is charged only on the present path. The actual
payload and selection equation remain available to its branch certificate. -/
theorem match_max {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {noneBound someBound : Nat}
    (noneCost : value.eval entry.locals = none →
      StmtArenaCostBound program w heapLimit depth noneBranch entry noneBound)
    (someCost : ∀ payload, value.eval entry.locals = some payload →
      StmtArenaCostBound program w heapLimit depth someBranch
        (Complexity.Language.State.cons payload entry) someBound) :
    StmtArenaCostBound program w heapLimit depth (.matchOption value noneBranch someBranch)
      entry (max (noneBound + 2) (2 * fieldCount τ + someBound + 3)) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | matchNone branch =>
      exact (Nat.add_le_add_right (noneCost (by assumption) _ _ branch) 2).trans
        (Nat.le_max_left _ _)
  | matchSome branch =>
      exact (Nat.add_le_add_right
        (Nat.add_le_add_left (someCost _ (by assumption) _ _ branch) (2 * fieldCount τ))
        3).trans (Nat.le_max_right _ _)

/-- A uniform function-body certificate bounds an actual allocating or
nonallocating call. The callee bound already includes its initialization;
the continuation uses its real returned value and final heap at the same depth. -/
theorem call_uniform {fn : Fin signatures.length}
    {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {calleeBound nextBound : Nat}
    (callee : FunctionArenaCostBound program (program.body fn) id (fun _ _ => True)
      w heapLimit depth (fun _ => calleeBound))
    (body : ∀ value heap, StmtArenaCostBound program w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1) (.call fn args continuation) entry
      (callCost program fn calleeBound + nextBound) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | callReturn calleeCost bodyCost =>
      have calleeLe := callee _ _ trivial _ _ _ _ calleeCost
      have bodyLe := body _ _ _ _ bodyCost
      exact Nat.add_le_add (callCost_mono program fn calleeLe) bodyLe

/-- Transport a uniform call rule across an equality of the actual signature. -/
theorem call_uniform_of_eq {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {calleeBound nextBound : Nat}
    (callee : FunctionArenaCostBound program
      (cast (congrArg (fun signature =>
        Complexity.Language.Stmt signatures signature.params signature.result) same)
          (program.body fn)) id (fun _ _ => True) w heapLimit depth (fun _ => calleeBound))
    (body : ∀ value heap, StmtArenaCostBound program w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) entry
      (callCost program fn calleeBound + nextBound) := by
  cases same
  exact call_uniform callee body

/-- Import a supplied uniform callee certificate through its actual program
embedding. Signature casts and call-frame work stay in this connection layer. -/
theorem call_uniform_imported {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram) {fn : Fin source.length}
    {args : Args Γ source[fn].params}
    {continuation : Complexity.Language.Stmt target (source[fn].result :: Γ) result}
    {calleeBound nextBound : Nat}
    (callee : FunctionArenaCostBound sourceProgram (sourceProgram.body fn) id (fun _ _ => True)
      w heapLimit depth (fun _ => calleeBound))
    (body : ∀ value heap, StmtArenaCostBound targetProgram w heapLimit (depth + 1) continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn) (map.signature_eq fn) args continuation)
      entry (callCost targetProgram (map.toFun fn) calleeBound + nextBound) := by
  refine call_uniform_of_eq (args := args) (entry := entry)
    (calleeBound := calleeBound) (nextBound := nextBound) (map.signature_eq fn) ?_ body
  have relocated := callee.renameCalls embedded
  rw [← embedded fn] at relocated
  exact relocated

/-- Legacy statement bounds transfer only when the existing read-only bridge
provides a realization of this actual execution and every actual callee. -/
theorem of_noHeapWrites (bounded : StmtCostBound program stmt entry bound)
    (readOnly : NoHeapWrites stmt) (callees : ∀ fn, NoHeapWrites (program.body fn)) :
    StmtArenaCostBound program w heapLimit depth stmt entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  let realized := ready.realized_of_noHeapWrites readOnly callees
  obtain ⟨legacySteps, legacyCost⟩ := realized.exists_cost
  have same : legacySteps = steps := (legacyCost.arena heapLimit cursor).deterministic cost
  exact same ▸ bounded realized legacyCost

end StmtArenaCostBound

/-- A structural body certificate supplies the existing function contract,
adding body initialization exactly once without adding a termination claim. -/
theorem FunctionArenaCostBound.of_stmt {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {Γ : List Ty} {result : Ty}
    {body : Complexity.Language.Stmt signatures Γ result}
    {args : X → Env Γ} {pre : X → Heap → Prop}
    {w heapLimit depth : Nat} {coreBound : X → Nat}
    (bounded : ∀ x heap, pre x heap →
      StmtArenaCostBound program w heapLimit depth body ⟨args x, heap⟩ (coreBound x)) :
    FunctionArenaCostBound program body args pre w heapLimit depth (fun x => coreBound x + 2) := by
  intro x heap allowed finish value execution cursor finalCursor ready steps cost
  exact Nat.add_le_add_right (bounded x heap allowed execution ready cost) 2

end Ram.LanguageCompiler
