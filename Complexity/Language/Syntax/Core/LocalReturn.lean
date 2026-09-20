/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Expression
import Complexity.Language.Eval.Locals.LocalReturn

/-!
# Internal local-return lowering and proof traces

Builds the existing optional-result boundary, gated continuations, loop guards and scratch-result
commit fragments. The paired proof traces follow these same source statements. This module does
not export generated contracts or decide the order of declaration emission.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def doSequence (elements : Array (TSyntax `doElem)) : TSyntax ``doSeq :=
  ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩

def LoweredBlock.proofSequence (block : LoweredBlock) (normal : TSyntax `doElem) :
    TSyntax ``doSeq :=
  doSequence (if block.fallsThrough then block.proofBody.push normal else block.proofBody)

def lookupProofBinding (scope : Scope) (name : Name) : MacroM (Binding × Nat) := do
  for (binding, index) in scope.zipIdx do
    if binding.proofName.getId == name then return (binding, index)
  Macro.throwError "a local-return slot is outside its lexical source scope"

def localReturnTarget (scope : Scope) (pending : TSyntax `ident) :
    MacroM LocalReturnTarget := do
  let (pendingBinding, _) ← lookupBinding scope pending
  let .option type := pendingBinding.type
    | Macro.throwErrorAt pending "a local-return result slot must have an Option type"
  unless pendingBinding.isMutable do
    Macro.throwErrorAt pending "a local-return result slot must be mutable"
  return ⟨type, pendingBinding.proofName.getId⟩

def localReturnCode (scope : Scope) (target : LocalReturnTarget)
    (value : TSyntax `term) : MacroM LoweredBlock := do
  let (pending, pendingIndex) ← lookupProofBinding scope target.pending
  let pendingVar ← variableTerm pendingIndex
  let parsed ← parsePrimitive scope value (some target.type)
  expectType value parsed.type target.type
  let term ← match parsed.atom with
    | some atom =>
        `(Complexity.Language.Stmt.LocalReturn.store $pendingVar $atom)
    | none =>
        `(Complexity.Language.Stmt.letPrim $(parsed.term)
          (Complexity.Language.Stmt.LocalReturn.store
            (Complexity.Language.Var.there $pendingVar)
            (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨term, #[
    ← `(doElem| $(pending.proofName):ident := some $(parsed.value))], true, #[]⟩

def resumeLocalCode (scope : Scope) (target : LocalReturnTarget)
    (next : LoweredBlock) : MacroM LoweredBlock := do
  let (pending, index) ← lookupProofBinding scope target.pending
  let atom ← `(Complexity.Language.Atom.var $(← variableTerm index))
  let body := next.proofSequence (← `(doElem| pure ()))
  return { next with
    term := ← `(Complexity.Language.Stmt.LocalReturn.resume $atom $(next.term))
    proofBody := #[← `(doElem| match $(pending.proofName):ident with
      | none => $body:doSeq
      | some _ => pure ())]
    fallsThrough := true }

def localGuard (scope : Scope) (target : Option LocalReturnTarget)
    (guard : TSyntax `term) : MacroM (TSyntax `term) := do
  let some target := target | return guard
  let (_, index) ← lookupProofBinding scope target.pending
  `(Complexity.Language.Stmt.LocalReturn.guard
    (Complexity.Language.Atom.var $(← variableTerm index)) $guard)

/-- Commit only after the child scope has returned normally. A failing scope
skips this fragment, and the enclosing lexical lets drop its private slots. -/
def commitLocalReturnCode (scope : Scope) (target : LocalReturnTarget)
    (childPending : Binding) : MacroM LoweredBlock := do
  let (pending, pendingIndex) ← lookupProofBinding scope target.pending
  let (_, childIndex) ← lookupProofBinding scope childPending.proofName.getId
  let value ← freshProofName childPending.proofName `localResult
  let pendingVar ← variableTerm pendingIndex
  let term ← `(Complexity.Language.Stmt.matchOption
    (Complexity.Language.Atom.var $(← variableTerm childIndex))
    Complexity.Language.Stmt.skip
    (Complexity.Language.Stmt.LocalReturn.store
      (Complexity.Language.Var.there $pendingVar)
      (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨term, #[← `(doElem| match $(childPending.proofName):ident with
    | none => pure ()
    | some $value:ident =>
        $(pending.proofName):ident := some $value:ident)], true, #[]⟩

def loopProofBody (site : BlockSite) : MacroM (Array (TSyntax `doElem)) := do
  let control ← freshProofName site.name `loopControl
  let locals ← freshProofName site.name `loopLocals
  let value ← freshProofName site.name `returned
  let error ← freshProofName site.name `error
  let invocation := scopeApplication site.scope site.name
  let mut elements := #[← `(doElem|
    let ($control:ident, $locals:ident) ← MonadLift.monadLift $invocation)]
  let fields ← tupleFields site.scope ⟨locals.raw⟩
  for binding in site.scope, field in fields do
    if binding.isMutable then
      elements := elements.push (← `(doElem| $(binding.proofName):ident := $field))
  -- An enclosing block must retain the actual final mutable values even when
  -- this nested block returns. These are pure local assignments, not heap writes.
  return elements.push (← `(doElem| match $control:ident with
    | .normal => pure ()
    | .returned $value:ident => return $value:ident
    | .fault $error:ident => throw $error:ident))

end Core

end Complexity.Language.Syntax
