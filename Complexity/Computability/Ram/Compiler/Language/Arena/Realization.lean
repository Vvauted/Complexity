/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization

/-!
# Allocation-aware readiness of an existing source execution

`ArenaReady` indexes the independent source `Exec`; it is additional word-range,
call-nesting and allocation-capacity evidence, not another execution relation.
Its cursor indices compose through actual guards, iterations, calls and lexical
continuations. A returning callee's final cursor is never reset to the caller's
entry cursor unless the source explicitly encloses that work in a reclaiming
scope. Allocation advances the cursor; successful scope exit restores its mark.

Positive cursors, physical object placement, rooted environments and the global
word-address bound remain premises of arena representation and simulation.
No memory model, out-of-memory outcome, cost, fuel or runtime stack is added here.
The fixed-placement realization interface embeds with an unchanged cursor and
without acquiring any of these separate representation premises.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Resource readiness of the same finite source execution. Successful branches
retain the original realization range conditions; allocation additionally threads
the reserved extent through its actual continuation, and a safe scope restores
its entry extent after its body has finished. -/
inductive ArenaReady {signatures : List Signature}
    {program : Complexity.Language.Program signatures} :
    {Γ : List Ty} → {result : Ty} →
      {stmt : Complexity.Language.Stmt signatures Γ result} →
      {entry finish : Complexity.Language.State Γ} → {control : Control result} →
      (execution : Complexity.Language.Exec program stmt entry finish control) →
      (w heapLimit depth next₀ next₁ : Nat) → Prop where
  | skip {Γ : List Ty} {result : Ty} {w heapLimit depth next : Nat}
      (entry : Complexity.Language.State Γ) :
      ArenaReady (program := program) (Complexity.Language.Exec.skip (result := result) entry)
        w heapLimit depth next next
  | assign {Γ : List Ty} {τ result : Ty} {w heapLimit depth next : Nat}
      (target : Var Γ τ) (value : Prim Γ τ) (entry : Complexity.Language.State Γ)
      (fits : PrimFits w entry.locals value) :
      ArenaReady (program := program)
        (Complexity.Language.Exec.assign (result := result) target value entry)
        w heapLimit depth next next
  | letPrim {Γ : List Ty} {τ result : Ty} {w heapLimit depth next₀ next₁ : Nat}
      {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
      {control : Control result}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons (value.eval entry.locals) entry) finish control}
      (fits : PrimFits w entry.locals value)
      (ready : ArenaReady body w heapLimit depth next₀ next₁) :
      ArenaReady (.letPrim body) w heapLimit depth next₀ next₁
  | read {Γ : List Ty} {result : Ty} {kind : CellTy} {w heapLimit depth next₀ next₁ : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (kind.toTy :: Γ)}
      {control : Control result} {value : CellValue kind}
      {loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) finish control}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (indexFits : index.eval entry.locals < 2 ^ w)
      (valueFits : ValueFits w (kind.toValue value))
      (ready : ArenaReady body w heapLimit depth next₀ next₁) :
      ArenaReady (.read loaded body) w heapLimit depth next₀ next₁
  | write {Γ : List Ty} {result : Ty} {kind : CellTy} {w heapLimit depth next : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : Complexity.Language.State Γ} {heap : Heap}
      {written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (indexFits : index.eval entry.locals < 2 ^ w)
      (valueFits : ValueFits w (value.eval entry.locals)) :
      ArenaReady (.write (result := result) written) w heapLimit depth next next
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy} {w heapLimit depth next₀ next₁ : Nat}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)}
      {control : Control result} {view : Buffer kind}
      {sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons view entry) finish control}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (offsetFits : offset.eval entry.locals < 2 ^ w)
      (lengthFits : length.eval entry.locals < 2 ^ w)
      (viewFits : ValueFits w (τ := .buffer kind) view)
      (ready : ArenaReady body w heapLimit depth next₀ next₁) :
      ArenaReady (.slice sliced body) w heapLimit depth next₀ next₁
  | alloc {Γ : List Ty} {result : Ty} {kind : CellTy} {w heapLimit depth next₀ next₁ : Nat}
      {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)} {control : Control result}
      {body : Complexity.Language.Exec program continuation
        (let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
          (kind.ofValue (initial.eval entry.locals))
         Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩)
        finish control}
      (initialFits : ValueFits w (initial.eval entry.locals))
      (capacity : next₀ + length.eval entry.locals ≤ heapLimit)
      (ready : ArenaReady body w heapLimit depth (next₀ + length.eval entry.locals) next₁) :
      ArenaReady (.alloc body) w heapLimit depth next₀ next₁
  | scope {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ bodyCursor : Nat}
      {stmt : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {body : Complexity.Language.Exec program stmt entry finish control}
      {safe : ScopeSafe entry.heap finish control}
      (ready : ArenaReady body w heapLimit depth next₀ bodyCursor) :
      ArenaReady (.scope body safe) w heapLimit depth next₀ next₀
  | seqNormal {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ middleCursor next₁ : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Complexity.Language.State Γ} {control : Control result}
      {head : Complexity.Language.Exec program first entry middle .normal}
      {tail : Complexity.Language.Exec program second middle finish control}
      (headReady : ArenaReady head w heapLimit depth next₀ middleCursor)
      (tailReady : ArenaReady tail w heapLimit depth middleCursor next₁) :
      ArenaReady (.seqNormal head tail) w heapLimit depth next₀ next₁
  | seqReturn {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ next₁ : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {value : Value result}
      {head : Complexity.Language.Exec program first entry finish (.returned value)}
      (ready : ArenaReady head w heapLimit depth next₀ next₁) :
      ArenaReady (.seqReturn (second := second) head) w heapLimit depth next₀ next₁
  | iteTrue {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ next₁ : Nat}
      {condition : Atom Γ .bool} {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = true}
      {body : Complexity.Language.Exec program yes entry finish control}
      (ready : ArenaReady body w heapLimit depth next₀ next₁) :
      ArenaReady (.iteTrue (no := no) test body) w heapLimit depth next₀ next₁
  | iteFalse {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ next₁ : Nat}
      {condition : Atom Γ .bool} {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = false}
      {body : Complexity.Language.Exec program no entry finish control}
      (ready : ArenaReady body w heapLimit depth next₀ next₁) :
      ArenaReady (.iteFalse (yes := yes) test body) w heapLimit depth next₀ next₁
  | whileFalse {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ}
      {test : Complexity.Language.Exec program guard entry finish (.returned false)}
      (ready : ArenaReady test w heapLimit depth next₀ next₁) :
      ArenaReady (.whileFalse (body := body) test) w heapLimit depth next₀ next₁
  | whileTrue {Γ : List Ty} {result : Ty}
      {w heapLimit depth next₀ guardCursor bodyCursor next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard afterBody finish : Complexity.Language.State Γ} {control : Control result}
      {test : Complexity.Language.Exec program guard entry afterGuard (.returned true)}
      {iteration : Complexity.Language.Exec program body afterGuard afterBody .normal}
      {rest : Complexity.Language.Exec program (.while guard body) afterBody finish control}
      (testReady : ArenaReady test w heapLimit depth next₀ guardCursor)
      (bodyReady : ArenaReady iteration w heapLimit depth guardCursor bodyCursor)
      (restReady : ArenaReady rest w heapLimit depth bodyCursor next₁) :
      ArenaReady (.whileTrue test iteration rest) w heapLimit depth next₀ next₁
  | whileReturn {Γ : List Ty} {result : Ty} {w heapLimit depth next₀ guardCursor next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard finish : Complexity.Language.State Γ} {value : Value result}
      {test : Complexity.Language.Exec program guard entry afterGuard (.returned true)}
      {iteration : Complexity.Language.Exec program body afterGuard finish (.returned value)}
      (testReady : ArenaReady test w heapLimit depth next₀ guardCursor)
      (bodyReady : ArenaReady iteration w heapLimit depth guardCursor next₁) :
      ArenaReady (.whileReturn test iteration) w heapLimit depth next₀ next₁
  | ret {Γ : List Ty} {result : Ty} {w heapLimit depth next : Nat}
      (value : Atom Γ result) (entry : Complexity.Language.State Γ)
      (fits : ValueFits w (value.eval entry.locals)) :
      ArenaReady (program := program) (.ret value entry) w heapLimit depth next next
  | callReturn {Γ : List Ty} {result : Ty}
      {w heapLimit depth next₀ calleeCursor next₁ : Nat} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {calleeFinish : Complexity.Language.State signatures[fn].params}
      {value : Value signatures[fn].result}
      {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
      {control : Control result}
      {callee : Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
      (arguments : EnvFits w (args.eval entry.locals))
      (calleeReady : ArenaReady callee w heapLimit depth next₀ calleeCursor)
      (bodyReady : ArenaReady body w heapLimit (depth + 1) calleeCursor next₁) :
      ArenaReady (.callReturn callee body) w heapLimit (depth + 1) next₀ next₁

namespace ArenaReady

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {control : Control result}
variable {execution : Complexity.Language.Exec program stmt entry finish control}
variable {w heapLimit depth next₀ next₁ : Nat}

/-- Add resource readiness to an independently successful scope execution.
Source semantics supplies its actual non-escape proof; the resource argument
checks only the existing body's ranges, nesting and transient allocation.
Its final temporary extent is released, including on a source early return. -/
theorem scope_of_exec {cursor : Nat}
    (execution : Complexity.Language.Exec program (.scope stmt) entry finish control)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish)
    (bodyReady : ∀ after outcome,
      ∀ body : Complexity.Language.Exec program stmt entry after outcome,
        outcome.Satisfies (fun _ => True) (fun _ _ => True) after →
          ∃ finalCursor, ArenaReady body w heapLimit depth cursor finalCursor) :
    ArenaReady execution w heapLimit depth cursor cursor := by
  cases execution with
  | scope body safe =>
      obtain ⟨finalCursor, ready⟩ := bodyReady _ _ body (by
        cases control <;> exact successful)
      exact .scope (safe := safe) ready
  | scopeEscape body escapes =>
      exact False.elim (Control.not_satisfies_scopeFailure _ _ _ _ successful)

/-- Readiness retains every actual returned value's range and rules out faults. -/
theorem outcome_fits (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    ControlFits w control := by
  induction ready with
  | skip => trivial
  | assign => trivial
  | letPrim fits ready ih => exact ih
  | read bufferFits indexFits valueFits ready ih => exact ih
  | write => trivial
  | slice bufferFits offsetFits lengthFits viewFits ready ih => exact ih
  | alloc initialFits capacity ready ih => exact ih
  | scope ready ih => exact ih
  | seqNormal headReady tailReady ihHead ihTail => exact ihTail
  | seqReturn ready ih => exact ih
  | iteTrue ready ih => exact ih
  | iteFalse ready ih => exact ih
  | whileFalse => trivial
  | whileTrue testReady bodyReady restReady ihTest ihBody ihRest => exact ihRest
  | whileReturn testReady bodyReady ihTest ihBody => exact ihBody
  | ret value entry fits => exact fits
  | callReturn arguments calleeReady bodyReady ihCallee ihBody => exact ihBody

/-- A complete statement retains at least its entry extent. A reclaiming scope
has equal entry and exit cursors; this is not monotonicity at every execution
prefix, since the scope's final release decreases the cursor used by its body. -/
theorem cursor_mono (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    next₀ ≤ next₁ := by
  induction ready with
  | skip => exact Nat.le_refl _
  | assign => exact Nat.le_refl _
  | letPrim fits ready ih => exact ih
  | read bufferFits indexFits valueFits ready ih => exact ih
  | write => exact Nat.le_refl _
  | slice bufferFits offsetFits lengthFits viewFits ready ih => exact ih
  | alloc initialFits capacity ready ih => exact (Nat.le_add_right _ _).trans ih
  | scope => exact Nat.le_refl _
  | seqNormal headReady tailReady ihHead ihTail => exact ihHead.trans ihTail
  | seqReturn ready ih => exact ih
  | iteTrue ready ih => exact ih
  | iteFalse ready ih => exact ih
  | whileFalse ready ih => exact ih
  | whileTrue testReady bodyReady restReady ihTest ihBody ihRest =>
      exact ihTest.trans (ihBody.trans ihRest)
  | whileReturn testReady bodyReady ihTest ihBody => exact ihTest.trans ihBody
  | ret => exact Nat.le_refl _
  | callReturn arguments calleeReady bodyReady ihCallee ihBody => exact ihCallee.trans ihBody

end ArenaReady

namespace RealizedExec

/-- Existing fixed-placement realization acquires no capacity, rootedness or
arena premises. It keeps any chosen numeric cursor unchanged. -/
theorem arenaReady {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : RealizedExec program w depth stmt entry finish control)
    (heapLimit next : Nat) : ArenaReady execution.erase w heapLimit depth next next := by
  induction execution with
  | skip entry => exact .skip entry
  | assign target value entry fits => exact .assign target value entry fits
  | letPrim fits body ih => exact .letPrim fits ih
  | read bufferFits indexFits loaded valueFits body ih =>
      exact .read (loaded := loaded) bufferFits indexFits valueFits ih
  | write bufferFits indexFits valueFits written =>
      exact .write (written := written) bufferFits indexFits valueFits
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih =>
      exact .slice (sliced := sliced) bufferFits offsetFits lengthFits viewFits ih
  | seqNormal head tail ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn head ih => exact .seqReturn ih
  | iteTrue test body ih => exact .iteTrue (test := test) ih
  | iteFalse test body ih => exact .iteFalse (test := test) ih
  | whileFalse test ih => exact .whileFalse ih
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact .whileTrue ihTest ihIteration ihRest
  | whileReturn test iteration ihTest ihIteration => exact .whileReturn ihTest ihIteration
  | ret value entry fits => exact .ret value entry fits
  | callReturn arguments callee body ihCallee ihBody => exact .callReturn arguments ihCallee ihBody

end RealizedExec
end Ram.LanguageCompiler
