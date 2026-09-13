/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Types
import Complexity.Language.Representation.List
import Complexity.Program.Deriving
import Lean.PrettyPrinter.Delaborator

/-!
# Types for the represented native frontend

Native arrays and linked lists retain their existing heap-indexed contents
relations. Closed records reuse the checked direct-field embedding generated
by the program-interface deriving machinery; their field layout is interpreted
recursively through the same represented types. No record decoder or heap-free
equivalence is installed, and a native record is not identified with its raw
tuple merely because the two have the same fields.
Record products retain componentwise relations even when every component is
scalar, matching the structural field representations rather than replacing
their conjunction by a tuple-equality representation.

This module resolves types and exposes direct-field metadata. Constructors,
projections, calls and their preservation proofs remain the responsibility of
the represented frontend. In particular, recognizing an array type does not
make mathematical array operations executable, and an unguarded heap reference
still has no default source value for a result join.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

/-- A pure identity layout remains distinct from a heap-backed representation
or a nominal record observed through its checked field embedding. -/
inductive NativeType where
  | pure (type : PureType)
  | list (kind : CellTy)
  | array (kind : CellTy)
  | prod (left right : NativeType)
  | option (payload : NativeType)
  | record (name : Name) (layout : NativeType) (embedding : Expr)

/-- The existing source type implementing this native mathematical view. -/
def NativeType.coreTy : NativeType → Ty
  | .pure type => type.coreTy
  | .list kind => .option (.node kind)
  | .array kind => .buffer kind
  | .prod left right => .prod left.coreTy right.coreTy
  | .option payload => .option payload.coreTy
  | .record _ layout _ => layout.coreTy

/-- The ordinary Lean type, retaining each record's nominal identity. -/
def NativeType.nativeType : NativeType → Expr
  | .pure type => type.nativeType
  | .list kind => mkApp (mkConst ``List [Level.zero])
      (match kind with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  | .array kind => mkApp (mkConst ``Array [Level.zero])
      (match kind with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  | .prod left right => mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
      left.nativeType right.nativeType
  | .option payload => mkApp (mkConst ``Option [Level.zero]) payload.nativeType
  | .record name _ _ => mkConst name

/-- Observe the actual source value in its current heap. Record field transport
composes existing relations; it neither reconstructs a record from an arbitrary
handle nor changes the heap at which its contents are observed. -/
def NativeType.representation : NativeType → Expr
  | .pure type => type.representation
  | .list kind => mkApp (mkConst ``Representation.list)
      (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)
  | .array kind => mkApp (mkConst ``Representation.array)
      (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)
  | .prod left right => mkAppN (mkConst ``Representation.prod [Level.zero, Level.zero])
      #[left.nativeType, right.nativeType, coreTypeExpr left.coreTy, coreTypeExpr right.coreTy,
        left.representation, right.representation]
  | .option payload => mkAppN (mkConst ``Representation.option [Level.zero])
      #[payload.nativeType, coreTypeExpr payload.coreTy, payload.representation]
  | .record name layout embedding =>
      mkAppN (mkConst ``Representation.comap [Level.zero, Level.zero])
        #[layout.nativeType, mkConst name, coreTypeExpr layout.coreTy,
          layout.representation, embedding]

/-- Only the existing pure identity layout can use a native value directly as
its raw source value. Even a scalar-only record needs its field correspondence. -/
def NativeType.isPure : NativeType → Bool
  | .pure _ => true
  | _ => false

private partial def scalarProduct : Ty → Bool
  | .nat | .bool | .unit => true
  | .prod left right => scalarProduct left && scalarProduct right
  | _ => false

private partial def resolveNativeTypeAux (type : Expr) (records : List Name)
    (structuredProducts : Bool) :
    TermElabM NativeType := do
  let type ← instantiateMVars type
  if type.hasFVar || type.hasMVar then
    throwError "native source types must be closed and fully inferred"
  let reduced ← whnf type
  if let .app (.const ``List _) element := reduced then
    if ← isDefEq element (mkConst ``Nat) then return .list .nat
    if ← isDefEq element (mkConst ``Bool) then return .list .bool
    throwError "native linked lists currently contain Nat or Bool cells"
  if let .app (.const ``Array _) element := reduced then
    if ← isDefEq element (mkConst ``Nat) then return .array .nat
    if ← isDefEq element (mkConst ``Bool) then return .array .bool
    throwError "native arrays currently contain Nat or Bool cells"
  if let .app (.const ``Option _) payload := reduced then
    return .option (← resolveNativeTypeAux payload records structuredProducts)
  if let .app (.app (.const ``Prod _) left) right := reduced then
    let left ← resolveNativeTypeAux left records structuredProducts
    let right ← resolveNativeTypeAux right records structuredProducts
    if structuredProducts || !(left.isPure && right.isPure) then return .prod left right
  if let .const name _ := reduced then
    if (getStructureInfo? (← getEnv) name).isSome then
      if records.contains name then
        throwError "recursive native record layouts are not supported: {name}"
      let embedding ← Complexity.Program.Deriving.ensureStructureEmbedding name
      let embeddingType ← inferType embedding
      let fieldsType := embeddingType.getAppArgs[1]!
      let layout ← resolveNativeTypeAux fieldsType (name :: records) true
      return .record name layout embedding
  let pureType ← resolvePureType type
  unless scalarProduct pureType.coreTy do
    throwError "this native operation frontend requires scalars, arrays, lists, \
      closed records and their products/options"
  unless ← isDefEq pureType.nativeType (mkApp (mkConst ``Value) (coreTypeExpr pureType.coreTy)) do
    throwError "native pure values must retain their existing scalar/product identity layout"
  return .pure pureType

/-- Resolve a closed native type through existing scalar/container relations or
the checked direct-field record embedding. Nested records are supported, while
recursive layouts are rejected. Record fields retain the closed, nondependent,
non-inherited restrictions of program-interface deriving. -/
def resolveNativeType (type : Expr) : TermElabM NativeType :=
  resolveNativeTypeAux type [] false

/-- Elaborate a native type annotation and retain its mathematical identity. -/
def resolveType (stx : TSyntax `term) : TermElabM NativeType := withRef stx do
  resolveNativeType (← elabType stx)

/-- One direct field in constructor order, with its actual projection and
resolved native layout. This metadata describes Lean declarations, not trusted
runtime operations. -/
structure RecordField where
  name : Name
  projection : Name
  type : NativeType

/-- Retrieve checked direct fields for constructor and projection lowering.
The same embedding is reused when program interfaces were already derived;
otherwise it is generated and checked by that existing machinery. -/
def recordFields (name : Name) : TermElabM (Array RecordField) := do
  discard <| Complexity.Program.Deriving.ensureStructureEmbedding name
  let env ← getEnv
  let some info := getStructureInfo? env name
    | throwError "native record fields require an ordinary Lean structure"
  let constructor := getStructureCtor env name
  forallTelescope constructor.type fun arguments _ => do
    let mut fields := #[]
    for argument in arguments, fieldName in info.fieldNames do
      let some field := getFieldInfo? env name fieldName
        | throwError "missing native record projection metadata for '{fieldName}'"
      let type ← resolveNativeTypeAux (← instantiateMVars (← inferType argument)) [name] true
      fields := fields.push { name := fieldName, projection := field.projFn, type }
    return fields

/-- Delaborate checked expressions with their full declaration names. -/
def termOfExpr (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options => options.setBool `pp.fullNames true) do
    PrettyPrinter.delab expression

/-- Surface source syntax for the actual existing core layout. -/
partial def rawTypeTerm : Ty → TermElabM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .node .nat => `(NodeRef Nat)
  | .node .bool => `(NodeRef Bool)
  | .buffer .nat => `(Buffer Nat)
  | .buffer .bool => `(Buffer Bool)
  | .prod left right => do `($(← rawTypeTerm left) × $(← rawTypeTerm right))
  | .option value => do `(Option $(← rawTypeTerm value))

/-- Real source initializers for supported join slots. An unguarded buffer or
node cannot be fabricated as a default value; it requires a real source handle. -/
partial def rawDefaultTerm : Ty → TermElabM (TSyntax `term)
  | .nat => `(0)
  | .bool => `(false)
  | .unit => `(())
  | .option _ => `(none)
  | .prod left right => do
      let left ← rawDefaultTerm left
      let right ← rawDefaultTerm right
      `(($left:term, $right:term))
  | .node _ | .buffer _ =>
      throwError "a native join cannot initialize an unguarded heap reference"

/-- The actual Lean type of a raw source value. -/
def actualTypeTerm (type : Ty) : TermElabM (TSyntax `term) := do
  `(Complexity.Language.Value $(← termOfExpr (coreTypeExpr type)))

/-- Type compatibility is nominal Lean equality, never equality of raw layouts. -/
def sameType (expected actual : NativeType) : MetaM Bool :=
  isDefEq expected.nativeType actual.nativeType

/-- Report a mismatch at the user's native expression or annotation. -/
def expect (site : Syntax) (expected actual : NativeType) : TermElabM Unit := do
  unless ← sameType expected actual do
    throwErrorAt site "expected native type {expected.nativeType}, found {actual.nativeType}"

end Complexity.Language.Syntax.Represented
