/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Basic
import Complexity.Language.Eval.Locals
import Mathlib.Logic.Equiv.Prod
import Std.Do.WP.SimpLemmas

/-!
# Internal source-emission context and lexical coordinates

The internal `Core` namespace holds resolved function, binding and block records, source type
quotation, generated names and lexical-coordinate syntax builders. These helpers are shared by
lowering and proof emission; they do not register executable declarations.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

/-- A resolved parameter shared by function preparation and call checking. -/
structure Parameter where
  name : TSyntax `ident
  type : Ty

structure NativeView where
  header : NativeHeader
  parameterTypes : Array (TSyntax `term)
  resultType : TSyntax `term
  parameterEncodings : Array (TSyntax `term)
  parameterRebuilds : Array (TSyntax `term)
  resultEncoding : TSyntax `term
  parameterEmbeddings : Array (TSyntax `term)
  resultEmbedding : TSyntax `term
  parameterEquivs : Array (TSyntax `term)
  resultEquiv : TSyntax `term
  simplifications : Array (TSyntax `ident)

structure Function where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  body : TSyntax `term
  termination : TSyntax ``Lean.Parser.Termination.suffix
  nativeView : Option NativeView := none

structure Callee where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  id : TSyntax `ident
  observation : TSyntax `ident
  fold : TSyntax `ident
  native : Option (TSyntax `ident) := none
  pureEquation : Option (TSyntax `ident) := none
  sourceName : Option Name := none

def Callee.hasName (callee : Callee) (name : Name) : Bool :=
  callee.name.getId == name || callee.sourceName == some name

structure ImportedProgram where
  name : TSyntax `ident
  family : Name
  functions : Array FunctionInfo

structure ImportEmbedding where
  source : ImportedProgram
  map : TSyntax `term
  proof : TSyntax `term

structure ImportDeclarations where
  declarations : Array Syntax
  program : TSyntax `term
  signatures : TSyntax `term
  embeddings : Array ImportEmbedding

structure NativeCoordinate where
  type : TSyntax `term
  equiv : TSyntax `term

structure Binding where
  name : Option Name
  proofName : TSyntax `ident
  type : Ty
  isMutable : Bool
  native : Option NativeCoordinate := none
  /-- A compiler completion slot, marked by its resolved lexical identity. -/
  privatePending : Bool := false

abbrev Scope := List Binding

structure LocalReturnTarget where
  type : Ty
  /-- A resolved lexical identity, not a source spelling that can be shadowed. -/
  pending : Name

structure Atomic where
  type : Ty
  term : TSyntax `term
  value : TSyntax `term

structure Primitive where
  type : Ty
  term : TSyntax `term
  atom : Option (TSyntax `term)
  value : TSyntax `term

structure FiniteRange where
  cursor : TSyntax `ident
  stop : TSyntax `term
  stride : TSyntax `term
  body : Array (TSyntax `doElem)
  fallsThrough : Bool
  /-- Guard and increment inspect a pending local result rather than ordinary range
  control. Keep the original range coordinates without claiming its model. -/
  localReturn : Bool := false

/-- A proof-side tag retaining the actual range-entry context for emission. -/
structure RangeRequest where
  tag : Name
  entryScope : Scope
  proofBody : Array (TSyntax `doElem)

structure BlockSite where
  name : TSyntax `ident
  scope : Scope
  result : Ty
  guard : Option (TSyntax `term)
  body : TSyntax `term
  finiteRange : Option FiniteRange
  nativeResult : Option NativeCoordinate := none
  rangeRequest : Option RangeRequest := none
  /-- The completion slot actually updated inside this named block. -/
  localReturn : Option LocalReturnTarget := none

def BlockSite.hasStandardRange (site : BlockSite) : Bool :=
  site.finiteRange.any (! ·.localReturn)

def standardRange (site : BlockSite) : MacroM FiniteRange := do
  let some range := site.finiteRange
    | Macro.throwErrorAt site.name "expected a finite source range"
  if range.localReturn then
    Macro.throwErrorAt site.name
      "a locally returning range requires its exit-aware contract, not the standard range model"
  return range

structure LoweredBlock where
  term : TSyntax `term
  proofBody : Array (TSyntax `doElem)
  fallsThrough : Bool
  sites : Array BlockSite

structure NormalizedValue where
  bindings : Array (TSyntax `doElem)
  value : TSyntax `term
  atomic : Bool

-- These witnesses justify the partial elaborator definitions; no translation
-- branch uses them as a default source expression.
private instance : Nonempty Atomic :=
  ⟨⟨.unit, ⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩,
    ⟨(mkCIdent ``Unit.unit).raw⟩⟩⟩

private instance : Nonempty Primitive :=
  ⟨⟨.unit, Lean.Syntax.mkCApp ``Complexity.Language.Prim.atom
      #[⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩],
    some ⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩,
    ⟨(mkCIdent ``Unit.unit).raw⟩⟩⟩

private instance : Nonempty LoweredBlock :=
  ⟨⟨⟨(mkCIdent ``Complexity.Language.Stmt.skip).raw⟩, #[], true, #[]⟩⟩

private instance : Nonempty NormalizedValue :=
  ⟨⟨#[], ⟨(mkCIdent ``Unit.unit).raw⟩, true⟩⟩

private instance : Nonempty Ty := ⟨.unit⟩

def typeName : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .buffer .nat => "Buffer Nat"
  | .buffer .bool => "Buffer Bool"
  | .node .nat => "NodeRef Nat"
  | .node .bool => "NodeRef Bool"
  | .prod left right => s!"({typeName left} × {typeName right})"
  | .option value => s!"Option ({typeName value})"

private def referenceType? (stx : TSyntax `term) : Option Ty :=
  match stx with
  | `(Buffer Nat) => some (.buffer .nat)
  | `(Buffer Bool) => some (.buffer .bool)
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.nat) => some (.buffer .nat)
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.bool) => some (.buffer .bool)
  | `(NodeRef Nat) => some (.node .nat)
  | `(NodeRef Bool) => some (.node .bool)
  | `(Complexity.Language.NodeRef Complexity.Language.CellTy.nat) => some (.node .nat)
  | `(Complexity.Language.NodeRef Complexity.Language.CellTy.bool) => some (.node .bool)
  | _ => none

partial def parseType (stx : TSyntax `term) : MacroM Ty := do
  if let some reference := referenceType? stx then return reference
  match stx with
  | `(source_native_type% ($raw) ($_native) via ($_equiv)) => parseType raw
  | `(source_native_type% ($raw) ($_native)) => parseType raw
  | `(($type:term)) => parseType type
  | `(Nat) => return .nat
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | `($left × $right) | `(Prod $left $right) =>
      return .prod (← parseType left) (← parseType right)
  | `(Option $value) => return .option (← parseType value)
  | _ =>
      Macro.throwErrorAt stx
        "supported source types are Nat, Bool, Unit, Buffer Nat/Bool, NodeRef Nat/Bool, products and Option"

def typeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Complexity.Language.Ty.nat)
  | .bool => `(Complexity.Language.Ty.bool)
  | .unit => `(Complexity.Language.Ty.unit)
  | .buffer .nat => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.bool)
  | .node .nat => `(Complexity.Language.Ty.node Complexity.Language.CellTy.nat)
  | .node .bool => `(Complexity.Language.Ty.node Complexity.Language.CellTy.bool)
  | .prod left right => do
      `(Complexity.Language.Ty.prod $(← typeTerm left) $(← typeTerm right))
  | .option value => do
      `(Complexity.Language.Ty.option $(← typeTerm value))

def valueTypeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .buffer .nat => `(Complexity.Language.Buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Buffer Complexity.Language.CellTy.bool)
  | .node .nat => `(Complexity.Language.NodeRef Complexity.Language.CellTy.nat)
  | .node .bool => `(Complexity.Language.NodeRef Complexity.Language.CellTy.bool)
  | .prod left right => do
      `($(← valueTypeTerm left) × $(← valueTypeTerm right))
  | .option value => do
      `(Option $(← valueTypeTerm value))

end Core

open Core

/-- Normalize the source's existing reference-type spellings before Lean type
elaboration, also inside products and options. This only changes annotations:
a raw handle is not converted to an array/list observation or constructed here. -/
def normalizeReferenceTypes (stx : TSyntax `term) : MacroM (TSyntax `term) := do
  return ⟨← stx.raw.replaceM fun node => do
    match referenceType? ⟨node⟩ with
    | some reference => return some (← valueTypeTerm reference).raw
    | none => return none⟩

namespace Core

def expectType (stx : Syntax) (actual expected : Ty) : MacroM Unit := do
  unless actual == expected do
    Macro.throwErrorAt stx s!"expected source type {typeName expected}, found {typeName actual}"

def parameterTypes (params : Array Parameter) : MacroM (TSyntax `term) := do
  let types ← params.mapM fun param => typeTerm param.type
  `([$types,*])

def generatedName (family : TSyntax `ident) (fn : TSyntax `ident)
    (suffix : String) : TSyntax `ident :=
  mkIdentFrom fn ((family.getId ++ fn.getId).appendAfter suffix)

def actionName (family fn : TSyntax `ident) (pureMode : Bool) : TSyntax `ident :=
  generatedName family fn (if pureMode then "_action" else "")

def freshProofName (ref : Syntax) (name : Name) : MacroM (TSyntax `ident) :=
  withFreshMacroScope do
    return mkIdentFrom ref (← Macro.addMacroScope name)

def loopMember (site : BlockSite) (name : String) : TSyntax `ident :=
  mkIdentFrom site.name (site.name.getId ++ Name.mkSimple name)

def namedSimpArgs (names : Array (TSyntax `ident)) :
    MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  names.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)

def constantSimpArgs (names : Array Name) :
    MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  namedSimpArgs (names.map mkCIdent)

def viewSimpArgs : MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  constantSimpArgs #[``Equiv.trans_apply, ``Equiv.symm_trans_apply, ``Equiv.prodCongr_apply,
    ``Equiv.prodCongr_symm, ``Equiv.refl_apply, ``Equiv.refl_symm, ``Equiv.symm_symm, ``Prod.map,
    ``Equiv.coe_fn_mk, ``Equiv.toFun_as_coe, ``Equiv.invFun_as_coe,
    ``Complexity.Language.Env.equivProd_apply, ``Complexity.Language.Env.equivProd_symm_apply,
    ``Complexity.Language.Env.equivUnit_apply, ``Complexity.Language.Env.equivUnit_symm_apply,
    ``Complexity.Language.Env.head, ``Complexity.Language.Env.get_tail]

def valueSimpArgs : MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  constantSimpArgs #[``Complexity.Language.Atom.eval, ``Complexity.Language.Prim.eval,
    ``Complexity.Language.Args.eval, ``Complexity.Language.CellTy.toValue,
    ``Complexity.Language.CellTy.ofValue, ``Complexity.Language.Env.cons_here,
    ``Complexity.Language.Env.cons_there, ``Complexity.Language.Env.head_cons,
    ``Complexity.Language.Env.tail_cons, ``Complexity.Language.Env.get_tail,
    ``Complexity.Language.Env.get_equivProd_symm,
    ``Complexity.Language.Env.set_here, ``Complexity.Language.Env.set_there, ``pure_bind]

def scopeTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let types ← scope.toArray.mapM fun binding => typeTerm binding.type
  `([$types,*])

def scopeTuple (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(())
  for binding in scope.reverse do
    values ← `(($(binding.proofName):ident, $values))
  return values

def scopeValueTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(Unit)
  for binding in scope.reverse do
    values ← `($(← valueTypeTerm binding.type) × $values)
  return values

def bindingNativeType (binding : Binding) : MacroM (TSyntax `term) :=
  match binding.native with
  | some native => pure native.type
  | none => valueTypeTerm binding.type

def scopeNativeTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(Unit)
  for binding in scope.reverse do
    values ← `($(← bindingNativeType binding) × $values)
  return values

def scopeNativeEquiv (scope : Scope) : MacroM (TSyntax `term) := do
  let mut equiv ← `(Equiv.refl Unit)
  for binding in scope.reverse do
    let head ← match binding.native with
      | some native => pure native.equiv
      | none => `(Equiv.refl $(← valueTypeTerm binding.type))
    equiv ← `(Equiv.prodCongr $head $equiv)
  return equiv

private def encodeNativeField (binding : Binding) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  match binding.native with
  | some native => `(($(native.equiv)) $value)
  | none => pure value

def decodeNativeField (binding : Binding) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  match binding.native with
  | some native => `(($(native.equiv)).symm $value)
  | none => pure value

def encodeNativeFields (scope : Scope) (values : Array (TSyntax `term)) :
    MacroM (Array (TSyntax `term)) :=
  (scope.toArray.zip values).mapM fun (binding, value) => encodeNativeField binding value

def scopeView (scope : Scope) : MacroM (TSyntax `term) := do
  let mut view ← `(Complexity.Language.Env.equivUnit)
  for _ in scope.reverse do
    view ← `(Complexity.Language.Env.equivProd.trans
      (Equiv.prodCongr (Equiv.refl _) $view))
  return view

def tupleFields (scope : Scope) (tuple : TSyntax `term) : MacroM (Array (TSyntax `term)) := do
  let mut current := tuple
  let mut fields := #[]
  for _ in scope do
    fields := fields.push (← `(($current).1))
    current ← `(($current).2)
  return fields

def fieldsTuple (fields : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut tuple ← `(())
  for field in fields.reverse do
    tuple ← `(($field, $tuple))
  return tuple

def tupleExtProof (scope : Scope) : MacroM (TSyntax `term) := do
  let mut proof ← `(Subsingleton.elim _ _)
  for _ in scope do
    proof ← `(Prod.ext rfl $proof)
  return proof

def splitScopeFields (scope : Scope) (fields : Array (TSyntax `term)) :
    Array (TSyntax `term) × Array (TSyntax `term) :=
  scope.toArray.zip fields |>.foldl (fun (mutable, captured) (binding, value) =>
    if binding.isMutable then (mutable.push value, captured) else (mutable, captured.push value)) (#[], #[])

def mergeScopeFields (scope : Scope) (mutable captured : Array (TSyntax `term)) :
    Array (TSyntax `term) := Id.run do
  let mut fields := #[]
  let mut mutableIndex := 0
  let mut capturedIndex := 0
  for binding in scope do
    if binding.isMutable then
      fields := fields.push mutable[mutableIndex]!
      mutableIndex := mutableIndex + 1
    else
      fields := fields.push captured[capturedIndex]!
      capturedIndex := capturedIndex + 1
  return fields

def freshMutableScope (site : BlockSite) (scopePrefix : String) : MacroM Scope :=
  site.scope.mapM fun binding => do
    if !binding.isMutable then return binding
    let name := Name.mkSimple (scopePrefix ++ binding.proofName.getId.eraseMacroScopes.toString)
    return { binding with proofName := ← freshProofName site.name name }

def bindMutableFields (scope : Scope) (tuple body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let fields ← tupleFields scope tuple
  let mut result := body
  for (binding, index) in scope.zipIdx.reverse do
    if binding.isMutable then
      result ← `(let $(binding.proofName):ident := $(fields[index]!); $result)
  return result

def mutableApplication (scope : Scope) (name : TSyntax `ident) (heap : TSyntax `term)
    (leading : Array (TSyntax `term) := #[]) : TSyntax `term :=
  Lean.Syntax.mkApp ⟨name.raw⟩ (leading ++
    (scope.toArray.filter (·.isMutable)).map (fun binding => ⟨binding.proofName.raw⟩) ++ #[heap])

def curryScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(fun ($(binding.proofName):ident : $(← valueTypeTerm binding.type)) => $result)
  return result

def quantifyScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(∀ ($(binding.proofName):ident : $(← valueTypeTerm binding.type)), $result)
  return result

def curryNativeScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(fun ($(binding.proofName):ident : $(← bindingNativeType binding)) => $result)
  return result

def quantifyNativeScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(∀ ($(binding.proofName):ident : $(← bindingNativeType binding)), $result)
  return result

def scopeApplication (scope : Scope) (name : TSyntax `ident) : TSyntax `term :=
  Lean.Syntax.mkApp ⟨name.raw⟩ (scope.toArray.map fun binding => ⟨binding.proofName.raw⟩)

def tupleApplication (scope : Scope) (name : TSyntax `ident) (tuple : TSyntax `term) :
    MacroM (TSyntax `term) := do
  return Lean.Syntax.mkApp ⟨name.raw⟩ (← tupleFields scope tuple)

def parseFunction (stx : TSyntax `sourceFunction) : MacroM Function := do
  let declaration ← parseDeclaration stx
  let params ← declaration.params.mapM fun parameter => do
    pure ({ name := parameter.name, type := ← parseType parameter.type } : Parameter)
  return ⟨declaration.name, params, ← parseType declaration.result, declaration.body,
    declaration.termination, none⟩

end Core

end Complexity.Language.Syntax
