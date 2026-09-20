/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Imports
import Complexity.Language.Syntax.Declaration
import Lean.Elab.Tactic.Conv.Basic
import Lean.Meta.Closure
import Lean.Elab.Do
import Lean.Parser.Do

/-!
# Source declaration syntax and checked metadata

Declares the shared surface syntax, checked source-coordinate metadata and its persistent
registry. The source commands are elaborated in `Core.Elaboration`; this module does not lower
statements or construct correctness claims. The `Core` namespace contains internal emission
metadata, not an additional supported frontend.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

/-- An already checked grouping of a generated loop's mutable locals and captures,
with the guard and body theorems that preserve those captures. -/
structure LoopCaptureCoordinates where
  /-- The raw or native capture-grouping equivalence. -/
  view : Name
  /-- Capture preservation on every actual guard exit. -/
  guardFrame : Name
  /-- Capture preservation on every actual body exit. -/
  bodyFrame : Name

/-- Checked coordinates and frame theorems for a loop with a local-result slot.
These declarations connect visible source locals to the same actual loop state;
they do not provide an invariant, termination argument or resource bound. -/
structure LoopCompletionCoordinates where
  view : Name
  visible : Name
  entry : Name
  pending : Name
  reconstruct : Name
  reconstructNone : Name
  guardFrame : Name
  bodyFrame : Name
  stoppedGuard : Name
  pendingEval : Name

/-- Checked coordinate and capture declarations belonging to one generated source loop.
The key is its actual `Code` declaration; no executable body or budget is stored here. -/
structure LoopCoordinates where
  rules : Array Name
  /-- Raw coordinates first, followed by native coordinates when generated. -/
  captures : Array LoopCaptureCoordinates
  /-- Present only for a loop whose actual control uses a pending local result. -/
  completion? : Option LoopCompletionCoordinates := none

/-- One actual lexical coordinate of a generated source block. The order retains
shadowed bindings and anonymous compiler locals; names alone do not identify slots. -/
structure SourceLocal where
  name : Option Name
  proofName : TSyntax `ident
  type : Ty
  isMutable : Bool

/-- The actual named loop selected by a proof-side range tag. These coordinates
describe already emitted source declarations; the tag neither changes execution
nor provides a correctness premise. Entry bindings use `entryScope`; the loop
bounds and body use `scope`, including the actual cursor and saved endpoints. -/
structure ActualRangeSite where
  tag : Name
  name : Name
  entryScope : Array SourceLocal
  scope : Array SourceLocal
  result : Ty
  cursorSlot : Nat
  stop : TSyntax `term
  stride : TSyntax `term
  /-- The complete range observation, including its actual entry bindings. -/
  proofBody : Array (TSyntax `doElem)
  /-- The named loop observation after its entry bindings have been established. -/
  loopProofBody : Array (TSyntax `doElem)
  /-- The actual iteration, including index binding and cursor advancement. -/
  bodyProofBody : Array (TSyntax `doElem)
  bodyFallsThrough : Bool
  /-- The guard and increment are controlled by an enclosing pending local result,
  so this site does not have the ordinary always-active range correspondence. -/
  localReturn : Bool := false

/-- The actual named loop selected by a proof-side while tag. Its coordinates
refer to the emitted source loop, not a separately lowered mathematical model.
A locally returning loop needs a completion-aware contract. -/
structure ActualWhileSite where
  tag : Name
  name : Name
  scope : Array SourceLocal
  result : Ty
  localReturn : Bool := false

/-- Actual source blocks requested by the proof pass. Tags select emitted
declarations without adding statements, locals or function calls. -/
structure ActualBlockSites where
  ranges : Array ActualRangeSite
  whiles : Array ActualWhileSite

private initialize loopCoordinatesExt :
    SimplePersistentEnvExtension (Name × LoopCoordinates) (NameMap LoopCoordinates) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
  }

/-- Find the checked coordinates registered for an actual generated loop body. -/
def getLoopCoordinates? (env : Environment) (code : Name) : Option LoopCoordinates :=
  (loopCoordinatesExt.getState env).find? code

namespace Core

structure LoopCaptureCoordinateRegistration where
  view : TSyntax `ident
  guardFrame : TSyntax `ident
  bodyFrame : TSyntax `ident

structure LoopCompletionCoordinateRegistration where
  view : TSyntax `ident
  visible : TSyntax `ident
  entry : TSyntax `ident
  pending : TSyntax `ident
  reconstruct : TSyntax `ident
  reconstructNone : TSyntax `ident
  guardFrame : TSyntax `ident
  bodyFrame : TSyntax `ident
  stoppedGuard : TSyntax `ident
  pendingEval : TSyntax `ident

structure LoopCoordinateRegistration where
  code : TSyntax `ident
  rules : Array (TSyntax `ident)
  captures : Array LoopCaptureCoordinateRegistration
  nativeTypes : Array (TSyntax `term)
  completion? : Option LoopCompletionCoordinateRegistration := none

partial def registeredTypeNames (type : Lean.Expr) : Lean.Meta.MetaM (Array Name) := do
  let type ← Lean.Meta.whnf type
  if let .const name _ := type then
    if let some info := getStructureTypeInfo? (← Lean.getEnv) name then
      let mut names := #[name ++ `sourceEncode, name ++ `sourceEmbedding,
        name ++ `sourceEquiv_apply, name ++ `sourceEquiv_symm_apply]
      for field in info.fields do
        names := names ++ (← registeredTypeNames field.type.nativeType)
      return names
  let mut names := #[]
  for argument in type.getAppArgs do
    names := names ++ (← registeredTypeNames argument)
  return names

def registerLoopCoordinates (entries : Array LoopCoordinateRegistration) :
    Lean.Elab.Command.CommandElabM Unit := do
  for entry in entries do
    let code ← Lean.resolveGlobalConstNoOverload entry.code
    let mut rules ← entry.rules.mapM (fun rule => Lean.resolveGlobalConstNoOverload rule)
    let captures : Array LoopCaptureCoordinates ← entry.captures.mapM fun capture => do
      let view ← Lean.resolveGlobalConstNoOverload capture.view
      let guardFrame ← Lean.resolveGlobalConstNoOverload capture.guardFrame
      let bodyFrame ← Lean.resolveGlobalConstNoOverload capture.bodyFrame
      return ⟨view, guardFrame, bodyFrame⟩
    let completion? : Option LoopCompletionCoordinates ← entry.completion?.mapM fun completion => do
      return {
        view := ← Lean.resolveGlobalConstNoOverload completion.view
        visible := ← Lean.resolveGlobalConstNoOverload completion.visible
        entry := ← Lean.resolveGlobalConstNoOverload completion.entry
        pending := ← Lean.resolveGlobalConstNoOverload completion.pending
        reconstruct := ← Lean.resolveGlobalConstNoOverload completion.reconstruct
        reconstructNone := ← Lean.resolveGlobalConstNoOverload completion.reconstructNone
        guardFrame := ← Lean.resolveGlobalConstNoOverload completion.guardFrame
        bodyFrame := ← Lean.resolveGlobalConstNoOverload completion.bodyFrame
        stoppedGuard := ← Lean.resolveGlobalConstNoOverload completion.stoppedGuard
        pendingEval := ← Lean.resolveGlobalConstNoOverload completion.pendingEval
      }
    let nativeRules ← Lean.Elab.Command.liftTermElabM do
      let mut names := #[]
      for type in entry.nativeTypes do
        let type ← Lean.Elab.Term.elabTermAndSynthesize type none
        names := names ++ (← registeredTypeNames type)
      return names
    for rule in nativeRules do
      unless rules.contains rule do
        -- These declarations have already been checked by `source_type` and the
        -- native-coordinate derivation; registration never adds a proof premise.
        discard <| Lean.getConstInfo rule
        rules := rules.push rule
    modifyEnv fun env => loopCoordinatesExt.addEntry env (code, { rules, captures, completion? })

end Core

/-- Declare a finite family of named, independently interpreted source functions. -/
syntax (name := sourceProgram) "source_program " ident " where" ppLine
  many1Indent(sourceFunction) : command

/-- Declare source functions with qualified calls into previously declared source programs. -/
syntax (name := importingSourceProgram) "source_program " ident " importing " ident,+ " where" ppLine
  many1Indent(sourceFunction) : command

-- Internal declarations for the operations used to implement the public
-- frontend itself. They use the same typed emitter without importing their
-- own higher-level operation adapters.
syntax (name := coreSourceProgram) "source_program% " ident " where" ppLine
  many1Indent(sourceFunction) : command

syntax (name := importingCoreSourceProgram)
  "source_program% " ident " importing " ident,+ " where" ppLine
  many1Indent(sourceFunction) : command

/-- Generate a native total value function and a proved corresponding scalar source program. -/
syntax (name := pureSourceProgram) "source_program " "(" &"pure" ") " ident " where" ppLine
  many1Indent(sourceFunction) : command

/-- A pure source family may call previously proved pure source functions. -/
syntax (name := importingPureSourceProgram)
  "source_program " "(" &"pure" ") " ident " importing " ident,+ " where" ppLine
  many1Indent(sourceFunction) : command

/-- A lexical allocation scope; returns still leave the enclosing source function. -/
syntax (name := sourceScratch) "with_scratch " "do " doSeq : doElem

-- Preserve finite-range origin until both source and native views are emitted.
syntax (name := sourceFiniteRange)
  "source_range% " "(" ident "," term "," term ")" " do " doSeq : doElem

-- Associate a proof view with the loop produced by the ordinary for lowering.
-- This marker introduces no source statement, local, function or loop number.
syntax (name := sourceRangeSite)
  "source_range_site% " ident " (" term "," term ")" " do " doSeq : doElem

-- Associate a proof view with the loop produced by ordinary while lowering.
syntax (name := sourceWhileSite)
  "source_while_site% " ident " (" term ")" " do " doSeq : doElem

/-- Internal local-return boundary using an already declared mutable optional
result. It lowers through ordinary source assignments and option branches. -/
syntax (name := sourceLocalReturn)
  "source_local_return% " "(" ident ")" " do " doSeq : doElem

-- Internal emission point: infer an equation from its checked proof instead of
-- inventing an unresolved right-hand side in a theorem header.
syntax (name := inferredSourceEquation) "source_equation% " ident " := " term : command

-- Pure layout temporaries remain real source primitives. They are absent from
-- the native view only when a registered operation reconstructs that view.
syntax (name := sourceRawValue) "source_raw_value% " "(" term ")" : term
syntax (name := sourceRawNativeValue) "source_raw_value% " "(" term ")" "(" term ")" : term

macro_rules
  | `(source_raw_value% ($value)) => pure value
  | `(source_raw_value% ($value) ($_native)) => pure value

-- Obtain the converter's equality directly, without transporting a separate
-- reflexive proposition through the same normalization.
syntax (name := sourceConversion) "source_conversion% " term " => "
  Lean.Parser.Tactic.Conv.convSeq : term

elab_rules : term
  | `(source_conversion% $term => $steps:convSeq) => do
      let lhs ← Lean.Elab.Term.elabTermAndSynthesize term none
      let (_, proof) ← (Lean.Elab.Tactic.Conv.convert lhs
        (Lean.Elab.Tactic.evalTactic steps)
        { elaborator := ``sourceConversion, recover := false }).run' { goals := [] }
      return proof

elab_rules : command
  | `(command| source_equation% $name:ident := $proof:term) => do
      let rawName := name.getId
      let currentNamespace ← getCurrNamespace
      let declName := if (`_root_).isPrefixOf rawName then
          rawName.replacePrefix `_root_ Name.anonymous
        else currentNamespace ++ rawName
      Lean.Elab.Command.liftTermElabM do
        let value ← Lean.Elab.Term.withoutErrToSorry <|
          Lean.Elab.Term.elabTermAndSynthesize proof none
        if (← Lean.Elab.Term.logUnassignedUsingErrorInfos (← Lean.Meta.getMVars value)) then
          Lean.Elab.throwAbortTerm
        let value ← Lean.instantiateMVars value
        let type ← Lean.instantiateMVars (← Lean.Meta.inferType value)
        -- Source locals are already curried. Use Lean's let-expanding closure
        -- strategy; the declaration below still kernel-checks the full proof.
        let closed ← Lean.Meta.Closure.mkValueTypeClosure type value (zetaDelta := true)
        -- Match ordinary theorem elaboration: share repeated expression nodes
        -- across the closed proposition and proof before kernel checking.
        let shared := ShareCommon.shareCommon' #[closed.type, closed.value]
        Lean.addDecl (.thmDecl {
          name := declName
          levelParams := closed.levelParams.toList
          type := shared[0]!
          value := shared[1]!
        })
        Lean.addDocStringCore declName
          "One source-block observation equation derived from the proved semantic composition rules."

end Complexity.Language.Syntax
