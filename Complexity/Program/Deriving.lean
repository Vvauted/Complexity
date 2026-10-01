/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayInput
import Complexity.Program.CharInput
import Complexity.Program.IntInput
import Complexity.Program.OptionArrayInput
import Complexity.Program.RaggedArrayInput
import Lean.Elab.Deriving.Basic
import Lean.EnvExtension
import Lean.Meta.AppBuilder
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.NatTable
import Lean.Structure

/-!
# Deriving fixed program interfaces for records and enumerations

An ordinary record can use `deriving Complexity.Program.Input` or
`deriving Complexity.Program.Output`. The handlers expose its direct fields as
a right-associated product and reuse the existing fixed field interfaces.
They generate `programView`, `programView_injective` and `programEmbedding`
once, shared by both handlers and the separate RAM input handler.
Supported field-column array layouts also induce fixed record-array interfaces.

The field view only projects existing data. It does not execute a host-side
algorithm, load inputs, select a desired answer, or register source-language
operations. In particular an array-bearing input record can describe the
mathematical interface of a program without becoming a supported native source
parameter. Input preparation retains the preloaded invocation boundary.

The current handlers accept closed, nondependent records without inherited
fields. Empty records use `Unit`; a single field is not wrapped in a product.
Each resulting tuple must already have the requested fixed interface.
Closed enumerations with nonempty, argument-free constructors use Lean's
constructor indices. Their checked embedding shares the existing natural layout;
invalid indices observe no constructor. No `DecidableEq` instance is required
for the layout itself, and no runtime decoder is registered.
-/

namespace Complexity.Program.Deriving

open Lean Meta Elab Command

private initialize structureViewExt : SimplePersistentEnvExtension Name (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state name => state.insert name name
    addImportedFn := mkStateFromImportedEntries (fun state name => state.insert name name) {}
  }

private initialize enumViewExt : SimplePersistentEnvExtension Name (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state name => state.insert name name
    addImportedFn := mkStateFromImportedEntries (fun state name => state.insert name name) {}
  }

private def fieldsType : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit)
  | [field] => pure field
  | field :: rest => do mkAppM ``Prod #[field, ← fieldsType rest]

private def fieldsValue : List Expr → MetaM Expr
  | [] => pure (mkConst ``Unit.unit)
  | [field] => pure field
  | field :: rest => do mkAppM ``Prod.mk #[field, ← fieldsValue rest]

private def tupleProjection (count index : Nat) (value : Expr) : MetaM Expr := do
  let mut projected := value
  for _ in [:index] do
    projected ← mkAppM ``Prod.snd #[projected]
  if index + 1 < count then mkAppM ``Prod.fst #[projected] else pure projected

private def addDefinition (name : Name) (type value : Expr) (doc : String) :
    TermElabM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  withOptions (Elab.async.set · false) do
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
    enableRealizationsForConst name
  addDocStringCore name doc

/-- Register a generated fixed interface as an ordinary global Lean instance. -/
def addInterfaceInstance (name : Name) (value : Expr) (doc : String) : TermElabM Unit := do
  if (← getEnv).contains name then
    throwError "program interface deriving would overwrite '{name}'"
  addDefinition name (← inferType value) value doc
  addInstance name AttributeKind.global (eval_prio default)

/-- Derive the lossless direct-field embedding once and reuse it across program
interface handlers. This generates no executable source operation. -/
def ensureStructureEmbedding (name : Name) : TermElabM Expr := do
  let env ← getEnv
  let embeddingName := name ++ `programEmbedding
  if ((structureViewExt.getState env).find? name).isSome then
    return mkConst embeddingName
  let some info := getStructureInfo? env name
    | throwError "program interface deriving expects an ordinary Lean structure"
  let inductInfo ← getConstInfoInduct name
  unless inductInfo.numParams == 0 && inductInfo.numIndices == 0 &&
      inductInfo.levelParams.isEmpty do
    throwError "program interface deriving currently requires a closed structure without parameters"
  unless info.parentInfo.isEmpty do
    throwError "program interface deriving currently requires direct fields without an extends clause"
  let constructor := getStructureCtor env name
  let nativeType := mkConst name
  let (types, projections) ← forallTelescope constructor.type fun arguments _ => do
    let mut types := #[]
    let mut projections := #[]
    for argument in arguments, fieldName in info.fieldNames do
      let type ← instantiateMVars (← inferType argument)
      if type.hasFVar then
        throwError "program interface deriving does not support dependent field '{fieldName}'"
      let some field := getFieldInfo? env name fieldName
        | throwError "missing projection metadata for program input field '{fieldName}'"
      types := types.push type
      projections := projections.push field.projFn
    return (types, projections)
  let tupleType ← fieldsType types.toList
  let viewName := name ++ `programView
  let injectiveName := name ++ `programView_injective
  for declarationName in #[viewName, injectiveName, embeddingName] do
    if env.contains declarationName then
      throwError "program interface deriving would overwrite '{declarationName}'"
  let view ← withLocalDeclD `value nativeType fun value => do
    let fields ← projections.toList.mapM fun projection => mkAppM projection #[value]
    mkLambdaFVars #[value] (← fieldsValue fields)
  addDefinition viewName (← mkArrow nativeType tupleType) view
    "The fixed direct-field view used by this record's program interfaces."
  let view := mkConst viewName
  let injective ← withLocalDeclD `left nativeType fun left =>
    withLocalDeclD `right nativeType fun right => do
      withLocalDeclD `same (← mkEq (mkApp view left) (mkApp view right)) fun same => do
        let mut result ← mkEqRefl (mkConst constructor.name)
        for index in [:projections.size] do
          let projection ← withLocalDeclD `tuple tupleType fun tuple => do
            mkLambdaFVars #[tuple] (← tupleProjection projections.size index tuple)
          result ← mkCongr result (← mkCongrArg projection same)
        mkLambdaFVars #[left, right, same] result
  let injectiveType ← instantiateMVars (← mkAppM ``Function.Injective #[view])
  let injective ← instantiateMVars injective
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := injectiveName, levelParams := [], type := injectiveType, value := injective })
    enableRealizationsForConst injectiveName
  addDocStringCore injectiveName
    "The direct-field program view preserves the original record's equality."
  let embedding ← mkAppM ``Function.Embedding.mk #[view, mkConst injectiveName]
  addDefinition embeddingName (← inferType embedding) embedding
    "The shared checked record-to-fields embedding for fixed program interfaces."
  modifyEnv fun env => structureViewExt.addEntry env name
  return mkConst embeddingName

/-- Recognize closed enumerations without replacing the existing Boolean layout.
Universe-polymorphic singleton types keep their existing unit presentation. -/
def isClosedEnum [Monad m] [MonadEnv m] [MonadError m] (name : Name) : m Bool := do
  if name == ``Bool || !(← isEnumType name) then return false
  let info ← getConstInfoInduct name
  return info.levelParams.isEmpty && info.type == mkSort (.succ .zero)

/-- Use Lean's constructor numbering for a closed enumeration. The local lookup
table only proves injectivity; it is not a source operation or runtime decoder. -/
def ensureEnumEmbedding (name : Name) : TermElabM Expr := do
  let env ← getEnv
  let embeddingName := name ++ `programEmbedding
  if ((enumViewExt.getState env).find? name).isSome then
    return mkConst embeddingName
  unless ← isClosedEnum name do
    throwError "program enumeration layouts require a closed Type with nonempty, \
      argument-free constructors; Bool retains its existing layout"
  let info ← getConstInfoInduct name
  let viewName := name ++ `programView
  let injectiveName := name ++ `programView_injective
  for declarationName in #[viewName, injectiveName, embeddingName] do
    if env.contains declarationName then
      throwError "program interface deriving would overwrite '{declarationName}'"
  let nativeType := mkConst name
  let index := mkConst (mkCtorIdxName name)
  addDefinition viewName (← inferType index) index
    "The canonical constructor index used by this enumeration's program interfaces."
  let view := mkConst viewName
  let (inverse, inverseProof) ← if env.contains (name ++ `ofNat_ctorIdx) then
      pure (mkConst (name ++ `ofNat), mkConst (name ++ `ofNat_ctorIdx))
    else do
      let constructors := info.ctors.toArray.map mkConst
      let inverse ← withLocalDeclD `index (mkConst ``Nat) fun index => do
        mkLambdaFVars #[index] (← mkNatLookupTable index nativeType constructors)
      let proof ← withLocalDeclD `value nativeType fun value => do
        let proposition ← mkEq (mkApp inverse (mkApp view value)) value
        let motive ← mkLambdaFVars #[value] proposition
        let cases := mkAppN (mkConst (mkCasesOnName name) [Level.zero]) #[motive, value]
        let proof := mkAppN cases (← constructors.mapM fun constructor => mkEqRefl constructor)
        mkLambdaFVars #[value] proof
      pure (inverse, proof)
  let injective ← mkAppOptM ``Function.LeftInverse.injective
    #[some nativeType, some (mkConst ``Nat), some inverse, some view, some inverseProof]
  let injectiveType ← mkAppM ``Function.Injective #[view]
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl {
      name := injectiveName, levelParams := [], type := injectiveType, value := injective })
    enableRealizationsForConst injectiveName
  addDocStringCore injectiveName
    "The constructor-index program view preserves the original enumeration's equality."
  let embedding ← mkAppM ``Function.Embedding.mk #[view, mkConst injectiveName]
  addDefinition embeddingName (← inferType embedding) embedding
    "The shared checked enumeration-to-natural embedding for fixed program interfaces."
  modifyEnv fun env => enumViewExt.addEntry env name
  return mkConst embeddingName

/-- Share canonical record fields or enumeration indices across fixed interfaces.
Ordinary empty structures retain their existing unit layout. -/
def ensureInterfaceEmbedding (name : Name) : TermElabM Expr := do
  if (getStructureInfo? (← getEnv) name).isSome then
    ensureStructureEmbedding name
  else
    ensureEnumEmbedding name

private def deriveInputPrefix (instanceName : Name) (view : Expr) :
    TermElabM Unit := do
  let tupleType := (← inferType view).getAppArgs[1]!
  let prefixValue ← withLocalDecl `Tail .implicit (mkSort (.succ .zero)) fun tail => do
    let target ← mkAppM ``Prod #[tupleType, tail]
    withLocalDecl `input .instImplicit (← mkAppM ``Input #[target]) fun input => do
      let tailView ← mkAppM ``Function.Embedding.refl #[tail]
      let fields ← mkAppM ``Function.Embedding.prodMap #[view, tailView]
      mkLambdaFVars #[tail, input] (← mkAppM ``Input.comap #[input, fields])
  addInterfaceInstance instanceName prefixValue
    "Prepend the same derived field layout to any registered input tail."
  let prefixClosed ← withLocalDecl `Tail .implicit (mkSort (.succ .zero)) fun tail => do
    let target ← mkAppM ``Prod #[tupleType, tail]
    withLocalDecl `input .instImplicit (← mkAppM ``Input #[target]) fun input => do
      withLocalDecl `closed .instImplicit (← mkAppOptM ``Input.PrefixClosed
          #[some target, some input]) fun closed => do
        let fields ← mkAppM ``Function.Embedding.prodMap
          #[view, ← mkAppM ``Function.Embedding.refl #[tail]]
        let value ← mkAppOptM ``Input.PrefixClosed.comap
          #[none, none, some input, some fields, some closed]
        mkLambdaFVars #[tail, input, closed] value
  addInterfaceInstance (instanceName.appendAfter "PrefixClosed") prefixClosed
    "Derived field prefixes retain observations under exact heap prefixes."

private def deriveArrayInput (name : Name) (embedding : Expr) (tupleType : Expr) :
    TermElabM Unit := do
  let arrayType ← mkAppM ``Array #[tupleType]
  let .some input ← trySynthInstance (← mkAppM ``Input #[arrayType]) | return
  let view ← mkAppM ``Function.Embedding.arrayMap #[embedding]
  let value ← mkAppM ``Input.comap #[input, view]
  addInterfaceInstance (name ++ `instProgramArrayInput) value
    "The fixed field-column input of an array of these records."
  if let .some closed ← trySynthInstance (← mkAppOptM ``Input.PrefixClosed
      #[some arrayType, some input]) then
    let value ← mkAppOptM ``Input.PrefixClosed.comap
      #[none, none, some input, some view, some closed]
    addInterfaceInstance (name ++ `instProgramArrayInputPrefixClosed) value
      "Record-array contents survive exact prefixes of the initial heap."
  deriveInputPrefix (name ++ `instProgramArrayInputProd) view

private def deriveInput (name : Name) : TermElabM Unit := do
  let embedding ← ensureInterfaceEmbedding name
  let type ← inferType embedding
  let tupleType := type.getAppArgs[1]!
  let input ← synthInstance (← mkAppM ``Input #[tupleType])
  let value ← mkAppM ``Input.comap #[input, embedding]
  addInterfaceInstance (name ++ `instProgramInput) value
    "The fixed program input obtained from this record's direct fields."
  let prefixType ← mkAppOptM ``Input.PrefixClosed #[some tupleType, some input]
  if let .some preserved ← trySynthInstance prefixType then
    let value ← mkAppOptM ``Input.PrefixClosed.comap
      #[some tupleType, some (mkConst name), some input, some embedding, some preserved]
    addInterfaceInstance (name ++ `instProgramInputPrefixClosed) value
      "The record input observation is preserved by an exact extension of its initial heap."
  deriveInputPrefix (name ++ `instProgramInputProd) embedding
  deriveArrayInput name embedding tupleType

private def deriveOutput (name : Name) : TermElabM Unit := do
  let embedding ← ensureInterfaceEmbedding name
  let type ← inferType embedding
  let tupleType := type.getAppArgs[1]!
  let output ← synthInstance (← mkAppM ``Output #[tupleType])
  let resultType ← mkAppOptM ``Output.type #[some tupleType, some output]
  let representation ← mkAppOptM ``Output.representation #[some tupleType, some output]
  let representation ← mkAppM ``Language.Representation.comap #[representation, embedding]
  let value ← mkAppOptM ``Output.mk #[some (mkConst name), some resultType, some representation]
  addInterfaceInstance (name ++ `instProgramOutput) value
    "Observe this record through its fields at the actual returned value and final heap."
  let arrayType ← mkAppM ``Array #[tupleType]
  if let .some output ← trySynthInstance (← mkAppM ``Output #[arrayType]) then
    let view ← mkAppM ``Function.Embedding.arrayMap #[embedding]
    let resultType ← mkAppOptM ``Output.type #[some arrayType, some output]
    let representation ← mkAppOptM ``Output.representation #[some arrayType, some output]
    let representation ← mkAppM ``Language.Representation.comap #[representation, view]
    let recordArray ← mkAppM ``Array #[mkConst name]
    let value ← mkAppOptM ``Output.mk #[some recordArray, some resultType, some representation]
    addInterfaceInstance (name ++ `instProgramArrayOutput) value
      "Observe an array of these records through its actual returned field columns."

private def inputHandler (names : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  unless ← names.allM (fun name => do
      return (getStructureInfo? env name).isSome || (← isClosedEnum name)) do
    return false
  for name in names do
    liftTermElabM (deriveInput name)
  return true

private def outputHandler (names : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  unless ← names.allM (fun name => do
      return (getStructureInfo? env name).isSome || (← isClosedEnum name)) do
    return false
  for name in names do
    liftTermElabM (deriveOutput name)
  return true

initialize registerDerivingHandler ``Input inputHandler
initialize registerDerivingHandler ``Output outputHandler

end Complexity.Program.Deriving
