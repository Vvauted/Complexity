/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Types
import Complexity.Language.Syntax.Core
import Complexity.Language.Representation.List
import Complexity.Language.Representation.RaggedArray
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

Arrays of supported products and nonempty records reuse their actual field
columns through one checked view. The resolver builds only array-unzip views
and pointwise direct-field record embeddings; it installs no arbitrary element
decoder. Nested arrays with scalar-column payloads keep one shared boundary
buffer and the existing payload layout. Empty record/Unit arrays, deeper ragged
payloads and unsupported nested element layouts remain rejected.

Existing raw `Buffer` and `NodeRef` parameters retain an identity observation
of the handle itself. This is distinct from an array or list contents relation;
handle equality supplies no validity, rootedness or bounds proof. Raw handles
are recognized before ordinary records and are never expanded into constructors.

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
  /-- Only resolver-recognized canonical scalar codes, never arbitrary free host encodings. -/
  | scalar (type embedding : Expr)
  | int
  | raw (type : Ty)
  | list (kind : CellTy)
  | array (kind : CellTy)
  | arrayProd (left right : CellTy)
  | raggedArray (payload : NativeType)
  | arrayView (element storage : NativeType) (embedding : Expr)
  | prod (left right : NativeType)
  | option (payload : NativeType)
  | record (name : Name) (layout : NativeType) (embedding : Expr)

/-- The existing source type implementing this native mathematical view. -/
def NativeType.coreTy : NativeType → Ty
  | .pure type => type.coreTy
  | .scalar _ _ => .nat
  | .int => .prod .bool .nat
  | .raw type => type
  | .list kind => .option (.node kind)
  | .array kind => .buffer kind
  | .arrayProd left right => .prod (.buffer left) (.buffer right)
  | .raggedArray payload => .prod (.buffer .nat) payload.coreTy
  | .arrayView _ storage _ => storage.coreTy
  | .prod left right => .prod left.coreTy right.coreTy
  | .option payload => .option payload.coreTy
  | .record _ layout _ => layout.coreTy

/-- The ordinary Lean type, retaining each record's nominal identity. -/
def NativeType.nativeType : NativeType → Expr
  | .pure type => type.nativeType
  | .scalar type _ => type
  | .int => mkConst ``Int
  | .raw type => mkApp (mkConst ``Value) (coreTypeExpr type)
  | .list kind => mkApp (mkConst ``List [Level.zero])
      (match kind with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  | .array kind => mkApp (mkConst ``Array [Level.zero])
      (match kind with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
  | .arrayProd left right => mkApp (mkConst ``Array [Level.zero])
      (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
        (match left with | .nat => mkConst ``Nat | .bool => mkConst ``Bool)
        (match right with | .nat => mkConst ``Nat | .bool => mkConst ``Bool))
  | .prod left right => mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
      left.nativeType right.nativeType
  | .raggedArray payload => mkApp (mkConst ``Array [Level.zero]) payload.nativeType
  | .arrayView element _ _ => mkApp (mkConst ``Array [Level.zero]) element.nativeType
  | .option payload => mkApp (mkConst ``Option [Level.zero]) payload.nativeType
  | .record name _ _ => mkConst name

/-- Observe the actual source value in its current heap. Record field transport
composes existing relations; it neither reconstructs a record from an arbitrary
handle nor changes the heap at which its contents are observed. -/
def NativeType.representation : NativeType → Expr
  | .pure type => type.representation
  | .scalar type embedding => mkAppN (mkConst ``Representation.ofEmbedding [Level.zero])
      #[type, coreTypeExpr .nat, embedding]
  | .int => mkConst ``Representation.int
  | .raw type =>
      let nativeType := mkApp (mkConst ``Value) (coreTypeExpr type)
      let embedding := mkApp (mkConst ``Function.Embedding.refl [Level.zero]) nativeType
      mkAppN (mkConst ``Representation.ofEmbedding [Level.zero])
        #[nativeType, coreTypeExpr type, embedding]
  | .list kind => mkApp (mkConst ``Representation.list)
      (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)
  | .array kind => mkApp (mkConst ``Representation.array)
      (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)
  | .arrayProd left right => mkAppN (mkConst ``Representation.arrayProd [Level.zero, Level.zero])
      #[(match left with | .nat => mkConst ``Nat | .bool => mkConst ``Bool),
        (match right with | .nat => mkConst ``Nat | .bool => mkConst ``Bool),
        coreTypeExpr (.buffer left), coreTypeExpr (.buffer right),
        mkApp (mkConst ``Representation.array)
          (match left with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool),
        mkApp (mkConst ``Representation.array)
          (match right with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)]
  | .prod left right => mkAppN (mkConst ``Representation.prod [Level.zero, Level.zero])
      #[left.nativeType, right.nativeType, coreTypeExpr left.coreTy, coreTypeExpr right.coreTy,
        left.representation, right.representation]
  | .raggedArray payload => mkAppN (mkConst ``Representation.raggedArrayOf [Level.zero])
      #[payload.nativeType.getAppArgs[0]!, coreTypeExpr payload.coreTy, payload.representation]
  | .arrayView element storage embedding =>
      mkAppN (mkConst ``Representation.comap [Level.zero, Level.zero])
        #[storage.nativeType, mkApp (mkConst ``Array [Level.zero]) element.nativeType,
          coreTypeExpr storage.coreTy, storage.representation, embedding]
  | .option payload => mkAppN (mkConst ``Representation.option [Level.zero])
      #[payload.nativeType, coreTypeExpr payload.coreTy, payload.representation]
  | .record name layout embedding =>
      mkAppN (mkConst ``Representation.comap [Level.zero, Level.zero])
        #[layout.nativeType, mkConst name, coreTypeExpr layout.coreTy,
          layout.representation, embedding]

/-- Identity layouts use the mathematical value directly as the source value.
For a raw handle this means handle equality, not heap-independent access to its
contents or absence of effects in functions using it. -/
def NativeType.isIdentity : NativeType → Bool
  | .pure _ | .raw _ => true
  | _ => false

/-- Compatibility name for the identity-representation test. This property is
about value observation, not a function's effects or successful termination. -/
abbrev NativeType.isPure := NativeType.isIdentity

/-- Supported array layouts retain heap-indexed observations. -/
def NativeType.isArray : NativeType → Bool
  | .array _ | .arrayProd _ _ | .raggedArray _ | .arrayView _ _ _ => true
  | _ => false

/-- Scalar column layouts can be sliced using one shared array of row boundaries.
Nested payload boundaries and linked nodes need different row operations. -/
def NativeType.hasScalarArrayColumns : NativeType → Bool
  | .array _ | .arrayProd _ _ => true
  | .arrayView _ storage _ => storage.hasScalarArrayColumns
  | .prod left right => left.hasScalarArrayColumns && right.hasScalarArrayColumns
  | _ => false

/-- Emit the actual scalar length observation of a supported array layout.
Product views select their first real column; record views retain the mapped
array's length. Only the checked unzip/map views built by the resolver use this
path. This neither decodes elements nor creates a source operation for a host map. -/
partial def NativeType.arraySizeTerm (type : NativeType) (raw : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  match type with
  | .array _ => `(($raw).$(mkIdent `length):ident)
  | .arrayProd _ _ =>
      let column ← `(Prod.fst $raw)
      `(($column).$(mkIdent `length):ident)
  | .raggedArray _ =>
      let column ← `(Prod.fst $raw)
      let length ← `(($column).$(mkIdent `length):ident)
      `($length - 1)
  | .arrayView _ (.prod left _) _ =>
      left.arraySizeTerm (← `(Prod.fst $raw))
  | .arrayView _ storage _ => storage.arraySizeTerm raw
  | _ => throwError "array size requires a supported nonempty field-column layout"

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
  if ← isDefEq reduced (mkConst ``Char) then
    return .scalar (mkConst ``Char) (mkConst ``Representation.charEmbedding)
  if ← isDefEq reduced (mkConst ``Int) then return .int
  if let .app (.const name _) kind := reduced then
    if name == ``Buffer || name == ``NodeRef then
      let cellKind ← if ← isDefEq kind (mkConst ``CellTy.nat) then pure CellTy.nat
        else if ← isDefEq kind (mkConst ``CellTy.bool) then pure CellTy.bool
        else throwError "raw source handles require a fixed Nat or Bool cell kind"
      return .raw (if name == ``Buffer then .buffer cellKind else .node cellKind)
  if let .app (.const ``List _) element := reduced then
    if ← isDefEq element (mkConst ``Nat) then return .list .nat
    if ← isDefEq element (mkConst ``Bool) then return .list .bool
    throwError "native linked lists currently contain Nat or Bool cells"
  if let .app (.const ``Array _) element := reduced then
    if ← isDefEq element (mkConst ``Nat) then return .array .nat
    if ← isDefEq element (mkConst ``Bool) then return .array .bool
    if ← isDefEq element (mkConst ``Char) then
      let embedding : Expr := mkConst ``Representation.charEmbedding
      return .arrayView (.scalar (mkConst ``Char) embedding) (.array .nat)
        (← mkAppM ``Function.Embedding.arrayMap #[embedding])
    if ← isDefEq element (mkConst ``Int) then
      let embedding ← mkAppM ``Function.Embedding.arrayMap
        #[← mkAppM ``Equiv.toEmbedding #[mkConst ``Representation.intEquiv]]
      return .arrayView .int (.arrayProd .bool .nat) embedding
    if let .app (.const ``Array _) _ ← whnf element then
      let payload ← resolveNativeTypeAux element records structuredProducts
      unless payload.hasScalarArrayColumns do
        throwError "native row reads require scalar-column payload arrays"
      return .raggedArray payload
    if let .app (.app (.const ``Prod _) left) right ← whnf element then
      let kind? (type : Expr) : TermElabM (Option CellTy) := do
        if ← isDefEq type (mkConst ``Nat) then return some .nat
        if ← isDefEq type (mkConst ``Bool) then return some .bool
        return none
      let leftKind ← kind? left
      let rightKind ← kind? right
      if let some leftKind := leftKind then
        if let some rightKind := rightKind then return .arrayProd leftKind rightKind
      let leftArray ← resolveNativeTypeAux
        (← mkAppM ``Array #[left]) records structuredProducts
      let rightArray ← resolveNativeTypeAux
        (← mkAppM ``Array #[right]) records structuredProducts
      let elementType ← resolveNativeTypeAux element records structuredProducts
      let embedding ← mkAppOptM ``Representation.arrayUnzip #[some left, some right]
      return .arrayView elementType (.prod leftArray rightArray) embedding
    if let .const name _ ← whnf element then
      if (getStructureInfo? (← getEnv) name).isSome then
        if records.contains name then
          throwError "recursive native record-array layouts are not supported: {name}"
        let embedding ← Complexity.Program.Deriving.ensureStructureEmbedding name
        let embeddingType ← inferType embedding
        let fieldsType := embeddingType.getAppArgs[1]!
        let storage ← resolveNativeTypeAux
          (← mkAppM ``Array #[fieldsType]) (name :: records) true
        let elementType ← resolveNativeTypeAux element records true
        let arrayEmbedding ← mkAppM ``Function.Embedding.arrayMap #[embedding]
        return .arrayView elementType storage arrayEmbedding
    throwError "native arrays require supported scalar, ragged, product or nonempty record fields"
  if let .app (.const ``Option _) payload := reduced then
    return .option (← resolveNativeTypeAux payload records structuredProducts)
  if let .app (.app (.const ``Prod _) left) right := reduced then
    let left ← resolveNativeTypeAux left records structuredProducts
    let right ← resolveNativeTypeAux right records structuredProducts
    let pureFields := match left, right with
      | .pure _, .pure _ => true
      | _, _ => false
    if structuredProducts || !pureFields then return .prod left right
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
      raw Buffer/NodeRef handles, closed records and their products/options"
  unless ← isDefEq pureType.nativeType (mkApp (mkConst ``Value) (coreTypeExpr pureType.coreTy)) do
    throwError "native pure values must retain their existing scalar/product identity layout"
  return .pure pureType

/-- Resolve a closed native type through existing scalar/container relations or
the checked direct-field record embedding. Nested records are supported, while
recursive layouts are rejected. Record fields retain the closed, nondependent,
non-inherited restrictions of program-interface deriving. -/
def resolveNativeType (type : Expr) : TermElabM NativeType :=
  resolveNativeTypeAux type [] false

/-- Normalize the existing raw-reference spellings, then elaborate the same
annotation and retain its mathematical identity through the shared resolver. -/
def resolveType (stx : TSyntax `term) : TermElabM NativeType := withRef stx do
  let normalized ← liftMacroM (normalizeReferenceTypes stx)
  resolveNativeType (← elabType normalized)

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

/-- Expand a pattern parsed by `checkedBindingPattern` over an already evaluated
value. Annotations are checked nominally, including on ignored fields; records
are not products merely because their source layouts are products. Untyped
projection bindings retain their resolved component observations. Nested
projection bases are shared, and unused fields produce no source bindings. -/
def patternBindings (pattern : BindingPattern) (type : NativeType)
    (value : TSyntax `term) : TermElabM (Array (TSyntax `doElem)) := do
  match pattern with
  | .wildcard => return #[]
  | .name name => return #[← `(doElem| let $name:ident := $value)]
  | .typed pattern annotation =>
      expect annotation (← resolveType annotation) type
      patternBindings pattern type value
  | .pair left right =>
      let (leftType, rightType) ← match type with
        | .prod left right => pure (left, right)
        | .pure pureType => do
            let .app (.app (.const ``Prod _) left) right ← whnf pureType.nativeType
              | throwErrorAt value "a product pattern requires a native product"
            pure (← resolveNativeType left, ← resolveNativeType right)
        | _ => throwErrorAt value "a product pattern requires a native product"
      let (bindings, base) ← if value.raw.isIdent then pure (#[], value) else do
        let name := mkIdent (← mkFreshUserName `pattern)
        pure (#[← `(doElem| let $name:ident := $value)],
          (⟨name.raw⟩ : TSyntax `term))
      let leftBindings ← patternBindings left leftType (← `(Prod.fst $base))
      let rightBindings ← patternBindings right rightType (← `(Prod.snd $base))
      let fields := leftBindings ++ rightBindings
      return if fields.isEmpty then #[] else bindings ++ fields

end Complexity.Language.Syntax.Represented
