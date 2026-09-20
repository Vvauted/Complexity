/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.LocalReturn
import Complexity.Language.Syntax.Pure

/-!
# Native value functions from buffer-free source blocks

Internal construction of the optional executable native view, including finite-range iteration
and dependency ordering. Native declarations use the same lowered source proof traces; their
correspondence proofs are emitted separately.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def pureValueType : Ty → Bool
  | .nat | .bool | .unit => true
  | .buffer _ | .node _ => false
  | .prod left right => pureValueType left && pureValueType right
  | .option value => pureValueType value

-- These identifiers were resolved by the source parser, and local proof
-- variables have fresh names. Replacing them cannot capture a source binder.
def pureProofElements (body : LoweredBlock) : Array (TSyntax `doElem) :=
  body.proofBody ++ body.sites.flatMap fun site =>
    site.finiteRange.map (·.body) |>.getD #[]

def rangeMutableScope (site : BlockSite) : Scope :=
  (site.scope.filter (·.isMutable)).drop 1

def nativeMarkedValue (value : TSyntax `term) : MacroM (TSyntax `term) := do
  let value ← value.raw.replaceM fun node => do
    match node with
    | `(source_native% ($_raw) ($native) ($_nativeType) via ($_equiv)) => return some native.raw
    | `(source_native% ($_raw) ($native) ($_nativeType)) => return some native.raw
    | `(source_native_type% ($_raw) ($native) via ($_equiv)) => return some native.raw
    | `(source_native_type% ($_raw) ($native)) => return some native.raw
    | _ => return none
  return ⟨value⟩

mutual

partial def nativeRangeStep (callees : Array Callee) (sites : Array BlockSite)
    (site : BlockSite) : MacroM (TSyntax `term) := do
  let range ← standardRange site
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeNativeTypes mutableScope
  let result ← match site.nativeResult with
    | some native => pure native.type
    | none => valueTypeTerm site.result
  let index ← freshProofName site.name `index
  let mutable ← freshProofName site.name `mutable
  let fields ← tupleFields mutableScope ⟨mutable.raw⟩
  let mut declarations := #[← `(doElem| let mut $(range.cursor):ident : Nat := $index:ident)]
  for binding in mutableScope, field in fields do
    declarations := declarations.push (← `(doElem|
      let mut $(binding.proofName):ident : $(← bindingNativeType binding) := $field))
  let returnedLocals ← scopeTuple mutableScope
  let iteration ← pureElements callees sites range.body (some returnedLocals)
  let ending ← if range.fallsThrough then do
      pure #[← `(doElem| return (none, $returnedLocals))]
    else pure #[]
  let body := doSequence (declarations ++ iteration ++ ending)
  return ← `(fun ($index:ident : Nat) ($mutable:ident : $mutableType) =>
    (Id.run (do $body:doSeq) : Option $result × $mutableType))

private partial def nativeRangeIteration (callees : Array Callee) (sites : Array BlockSite)
    (site : BlockSite) (positive : Option (TSyntax `term) := none) :
    MacroM (TSyntax `term) := do
  let range ← standardRange site
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeNativeTypes mutableScope
  let result ← match site.nativeResult with
    | some native => pure native.type
    | none => valueTypeTerm site.result
  let step ← nativeRangeStep callees sites site
  let positive ← match positive with
    | some proof => pure proof
    | none => `(by
        simp (config := { zetaDelta := true, failIfUnchanged := false }) only
          [Nat.add_eq] <;> omega)
  let start : TSyntax `term := ⟨range.cursor.raw⟩
  let initial ← scopeTuple mutableScope
  return ← `(Id.run (forIn (m := Id)
    ({ start := $start, stop := $(range.stop), step := $(range.stride), step_pos := $positive } : Std.Legacy.Range)
    ((none, ($start, $initial)) : Option $result × (Nat × $mutableType))
    (fun index state =>
      let outcome := ($step:term) index state.2.2
      outcome.1.elim (pure (ForInStep.yield (none, (index + $(range.stride), outcome.2))))
        (fun value => pure (ForInStep.done (some value, (index, outcome.2)))))))

partial def nativeRangeValue (callees : Array Callee) (sites : Array BlockSite)
    (site : BlockSite) (positive : Option (TSyntax `term) := none) :
    MacroM (TSyntax `term) := do
  let outcome ← freshProofName site.name `outcome
  let iteration ← nativeRangeIteration callees sites site positive
  let mutableFields ← tupleFields (site.scope.filter (·.isMutable))
    (← `(($outcome:ident).2))
  let capturedFields := (site.scope.filter (! ·.isMutable)).toArray.map
    fun binding => (⟨binding.proofName.raw⟩ : TSyntax `term)
  let locals ← fieldsTuple (mergeScopeFields site.scope mutableFields capturedFields)
  return ← `(let $outcome:ident := $iteration; (($outcome:ident).1, $locals))

private partial def pureElements (callees : Array Callee) (sites : Array BlockSite)
    (body : Array (TSyntax `doElem)) (returnedLocals : Option (TSyntax `term) := none) :
    MacroM (Array (TSyntax `doElem)) := do
  let mut elements := #[]
  for element in body do
    let replaced ← element.raw.replaceM fun node => do
      match node with
      | `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($_raw) ($native)) =>
          return some (← `(doElem| let $name:ident $[: $type:term]? := $native)).raw
      | `(doElem| let $_name:ident $[: $_type:term]? := source_raw_value% ($_raw)) =>
          return some (← `(doElem| pure ())).raw
      | `(source_native% ($_raw) ($native) ($_nativeType) via ($_equiv)) => return some native.raw
      | `(source_native% ($_raw) ($native) ($_nativeType)) => return some native.raw
      | `(source_native_type% ($_raw) ($native) via ($_equiv)) => return some native.raw
      | `(source_native_type% ($_raw) ($native)) => return some native.raw
      | `(doElem| let ($control:ident, $locals:ident) ← MonadLift.monadLift $invocation:term) =>
          if let some site := sites.find? (fun site => invocation.raw.hasIdent site.name.getId) then
            return some (← `(doElem| let ($control:ident, $locals:ident) :=
              $(← nativeRangeValue callees sites site))).raw
      | `(doElem| match $control:ident with
          | .normal => pure ()
          | .returned $value:ident => return $returned:term
          | .fault $_error:ident => throw $_thrown:term) =>
          let returned ← match returnedLocals with
            | none => pure returned
            | some locals => `((some $returned, $locals))
          return some (← `(doElem| match $control:ident with
            | none => pure ()
            | some $value:ident => return $returned)).raw
      | `(doElem| return $value:term) =>
          if let some locals := returnedLocals then
            let value ← nativeMarkedValue value
            return some (← `(doElem| return (some $value, $locals))).raw
      | _ => pure ()
      if node.isIdent then
        if let some callee := callees.find? (fun fn => fn.observation.getId == node.getId) then
          let some native := callee.native
            | Macro.throwErrorAt node
                "a pure source function can only call another proved pure source function"
          return some native.raw
      return none
    elements := elements.push (⟨replaced⟩ : TSyntax `doElem)
  return elements

end

private def pureBody (callees : Array Callee) (body : LoweredBlock) :
    MacroM (TSyntax ``doSeq) := do
  return doSequence (← pureElements callees body.sites body.proofBody)

-- Native Lean checks each self-recursive definition. Acyclic inter-function
-- calls are emitted in dependency order, including forward source references.
def pureFunctionOrder (family : TSyntax `ident) (functions : Array Function)
    (bodies : Array LoweredBlock) : MacroM (Array (Function × LoweredBlock)) := do
  let mut pending := (functions.zip bodies).toList
  let mut ordered : Array (Function × LoweredBlock) := #[]
  while !pending.isEmpty do
    let some next := pending.find? (fun (fn, body) =>
        pending.all fun (dependency, _) => dependency.name.getId == fn.name.getId ||
          !(pureProofElements body).any
            (fun element => element.raw.hasIdent
              (actionName family dependency.name true).getId))
      | Macro.throwErrorAt family
          "the pure frontend currently supports self recursion and acyclic named calls, not mutually recursive families"
    ordered := ordered.push next
    pending := pending.filter (fun entry => entry.1.name.getId != next.1.name.getId)
  return ordered

def nativeDeclaration (family : TSyntax `ident) (fn : Function)
    (callees : Array Callee) (body : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name ""
  let parameters ← fn.params.mapIdxM fun index param => do
    let parameterType ← match fn.nativeView with
      | some view => pure view.parameterTypes[index]!
      | none => valueTypeTerm param.type
    `(bracketedBinder| ($(param.name):ident : $parameterType))
  let result ← match fn.nativeView with
    | some view => pure view.resultType
    | none => valueTypeTerm fn.result
  let nativeBody ← pureBody callees body
  return (← `(command|
    /-- Executable total value function generated from the same buffer-free source block. -/
    def $name:ident $parameters:bracketedBinder* : $result :=
      Id.run (do $nativeBody:doSeq)
      $(fn.termination):suffix)).raw

end Core

end Complexity.Language.Syntax
