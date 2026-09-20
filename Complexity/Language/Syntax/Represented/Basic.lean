/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Types
import Complexity.Language.Syntax.Represented.Imports

/-!
# Prepared data for represented source programs

Naming policies, lexical bindings, optional mathematical models and proof traces
shared by represented source preparation and correspondence generation. The
`Internal` namespace contains implementation data, not an additional source
semantics or public program interface.
-/

namespace Complexity.Language.Syntax.Represented

open Lean Meta Elab Term Command
open Lean.Parser.Term

/-- Names of one source declaration and its optional mathematical proof view.
These names select no alternate evaluator or compilation path. -/
structure DeclarationNames where
  /-- Namespace of the public interfaces and generated correspondence theorems. -/
  publicFamily : TSyntax `ident
  /-- Namespace of the actual source table and actions. -/
  sourceFamily : TSyntax `ident
  /-- Suffix of the optional mathematical function, relative to its source name. -/
  modelSuffix : String

/-- Compatibility layout: source actions live under `Family.Source`, while the
ordinary mathematical function keeps the public name `Family.f`. -/
def DeclarationNames.native (family : TSyntax `ident) : DeclarationNames := {
  publicFamily := family
  sourceFamily := mkIdentFrom family (family.getId ++ `Source)
  modelSuffix := "" }

/-- Direct source layout: `Family.f` remains the actual action and an optional
checked mathematical function is named `Family.f_model`. -/
def DeclarationNames.source (family : TSyntax `ident) : DeclarationNames := {
  publicFamily := family, sourceFamily := family, modelSuffix := "_model" }

namespace Internal

structure Parameter where
  name : TSyntax `ident
  /-- Hygienic mathematical local; source syntax continues to use `name`. -/
  nativeName : TSyntax `ident := name
  type : NativeType
  rawName : TSyntax `ident
  relationName : TSyntax `ident
  /-- Stable lexical slot; assignment changes its value, not its identity. -/
  slot : Name := rawName.getId

inductive Observation where
  | refl
  | named (name : Name)
  | nil (kind : CellTy)
  | pair (purePair : Bool) (left right : Observation)
  | projection (purePair : Bool) (first : Bool) (pair : Observation)
  | none (payload : NativeType)
  | some (payload : Observation)
  | unary (operation : TSyntax `term) (argument : Observation)
  | binary (operation : TSyntax `term) (left right : Observation)
  | arraySize (array : Observation)

structure RetainedObservation where
  name : Name
  type : NativeType
  proof : TSyntax `term

structure BindingModel where
  model : TSyntax `term
  rawModel : TSyntax `term
  observation : Observation := .refl

structure Binding extends Parameter where
  model? : Option BindingModel := none
  mutable : Bool := false

structure Callback where
  sourceFamily : Name
  sourceName : Name
  nativeName : Name
  accumulator : NativeType
  kind : CellTy
  relation : Option Name := none

structure OperationModel where
  native : TSyntax `term
  equation : Option (TSyntax `ident)
  relation : TSyntax `ident
  refinement : TSyntax `ident
  preservingRelation : Option (TSyntax `ident) := none

/-- Actual source identity and mathematical types do not require a total-function
model. Model names are checked before they enter the public function registry. -/
structure Operation where
  family : TSyntax `ident
  sourceName : Name
  inputs : Array NativeType
  result : NativeType
  model? : Option OperationModel := none
  /-- A local mathematical candidate, resolved before any model declaration or
  public registration. It promises neither an equation nor a heap frame. -/
  modelDependency? : Option Name := none
  /-- Proof-side observation only; the source call still uses `sourceName`. -/
  actionName : Option Name := none

structure FoldRegistration where
  callback : Callback
  operation : Operation

structure ConsRegistration where
  kind : CellTy
  operation : Operation

structure UnconsRegistration where
  kind : CellTy
  operation : Operation

structure IsEmptyRegistration where
  kind : CellTy
  operation : Operation

structure ValueModel extends BindingModel where
  native : TSyntax `term

structure Value where
  type : NativeType
  raw : TSyntax `term
  model? : Option ValueModel := none

/-- Absence propagates through source preparation, without catching elaboration
or correspondence failures. -/
def mapModelsM {α β γ : Type} (left : Option α) (right : Option β)
    (f : α → β → TermElabM γ) : TermElabM (Option γ) := do
  match left, right with
  | some left, some right => return some (← f left right)
  | _, _ => return none

def Value.requireModel (value : Value) : TermElabM ValueModel := do
  let some model := value.model?
    | throwError "internal correspondence construction requires a prepared value model"
  return model

def Binding.requireModel (binding : Binding) : TermElabM BindingModel := do
  let some model := binding.model?
    | throwError "internal correspondence construction requires a prepared binding model"
  return model

def Operation.requireModel (operation : Operation) : TermElabM OperationModel := do
  let some model := operation.model?
    | throwError "internal correspondence construction requires a prepared operation model"
  return model

structure Invocation where
  operation : Operation
  arguments : Array Value
  result : Binding

/-- Proof composition retains alternatives instead of treating both as executed calls. -/
inductive Trace where
  | call (invocation : Invocation)
  | conditional (condition : Value) (yes no : Array Trace)
      (yesResult noResult : Value) (result : Binding)
  | optionMatch (discriminant : Value) (payload : Binding) (none some : Array Trace)
      (noneResult someResult : Value) (result : Binding)
  /-- A proof of the original named range, not a new source call. -/
  | range (tag : Name) (arguments : Array Value) (result : Binding) (preserving : Bool)

/-- A range either folds its continuing state or retains its optional local
result together with that state. Both are proof views of the same source loop. -/
inductive RangeModel where
  | fold (embedding mutableStep initialMutable indices : TSyntax `term)
  | completion (resultType : NativeType)

structure RangeRegistration where
  tag : Name
  captured : Array Binding
  state : Binding
  index : Binding
  body : Array Trace
  returned : Value
  bodyNative : TSyntax `term
  start : Value
  stop : Value
  stride : Value
  result : Binding
  model : RangeModel
  site? : Option ActualRangeSite := none

/-- Mathematical local types for an actual while site, independent of an
optional pure guard/body model or an array-preservation summary. -/
structure WhileLocalRegistration where
  tag : Name
  captured : Array Binding
  state : Binding
  site? : Option ActualWhileSite := none

/-- A single while round can have mathematical observations even when the
complete loop has no total-function model. These are proofs of the existing
guard and normal body, not separately emitted source functions. -/
structure WhileRegistration extends WhileLocalRegistration where
  guard : Array Trace
  guardResult : Value
  guardNative : TSyntax `term
  body : Array Trace
  returned : Value
  bodyNative : TSyntax `term

structure FunctionModel where
  nativeBody : TSyntax `term
  calls : Array Trace
  returned : Value
  termination : TSyntax ``Lean.Parser.Termination.suffix
  recursive : Bool := false

structure Function where
  name : TSyntax `ident
  parameters : Array Parameter
  result : NativeType
  rawBody : TSyntax `term
  model? : Option FunctionModel := none
  exposed : Bool := true

partial def Trace.hasExactEquation : Trace → Bool
  | .call invocation => PureImport.hasEncoding invocation.result.type &&
      invocation.operation.model?.any (·.equation.isSome)
  | .conditional _ yes no _ _ result => PureImport.hasEncoding result.type &&
      yes.all Trace.hasExactEquation && no.all Trace.hasExactEquation
  | .optionMatch _ _ absent present _ _ result => PureImport.hasEncoding result.type &&
      absent.all Trace.hasExactEquation && present.all Trace.hasExactEquation
  | .range .. => false

def Function.hasExactEquation (fn : Function) : Bool :=
  match fn.model? with
  | none => false
  | some model => !model.recursive && PureImport.hasEncoding fn.result &&
      model.calls.all Trace.hasExactEquation

partial def Trace.preservesArrays : Trace → Bool
  | .call invocation => invocation.operation.model?.any (·.preservingRelation.isSome)
  | .conditional _ yes no _ _ _ => yes.all Trace.preservesArrays && no.all Trace.preservesArrays
  | .optionMatch _ _ absent present _ _ _ =>
      absent.all Trace.preservesArrays && present.all Trace.preservesArrays
  | .range _ _ _ preserving => preserving

partial def Trace.containsRange : Trace → Bool
  | .range .. => true
  | .conditional _ yes no _ _ _ => yes.any Trace.containsRange || no.any Trace.containsRange
  | .optionMatch _ _ absent present _ _ _ =>
      absent.any Trace.containsRange || present.any Trace.containsRange
  | .call _ => false

def Function.preservesArrays (fn : Function) : Bool :=
  match fn.model? with
  | none => false
  | some model => fn.hasExactEquation || model.calls.all Trace.preservesArrays

/-- Every local signature is available before any body or model is prepared. -/
structure LocalHeader where
  name : TSyntax `ident
  parameters : Array (Name × NativeType)
  result : NativeType

structure Preparation where
  folds : Array FoldRegistration := #[]
  constructors : Array ConsRegistration := #[]
  deconstructors : Array UnconsRegistration := #[]
  emptinessTests : Array IsEmptyRegistration := #[]
  functions : Array Function := #[]
  ranges : Array RangeRegistration := #[]
  whiles : Array WhileRegistration := #[]
  /-- Completion-aware local interfaces do not require a pure round trace. -/
  completionWhiles : Array WhileLocalRegistration := #[]
  localHeaders : Array LocalHeader := #[]
  calledFamilies : Array (TSyntax `ident) := #[]
  current : Option Operation := none
  currentRecursive : Bool := false
  /-- Actual assignment identities, used to invalidate enclosing value-block views. -/
  assignedSlots : Array Name := #[]

abbrev PrepareM := StateT Preparation TermElabM

def prepareMacro {α : Type} (action : MacroM α) : PrepareM α :=
  liftM (liftMacroM action : TermElabM α)

def fieldName (family name : TSyntax `ident) (suffix : String := "") : TSyntax `ident :=
  mkIdentFrom name ((family.getId ++ name.getId).appendAfter suffix)
def modelName (names : DeclarationNames) (name : TSyntax `ident) :
    TSyntax `ident :=
  fieldName names.publicFamily name names.modelSuffix
def kindTerm (kind : CellTy) : TermElabM (TSyntax `term) :=
  termOfExpr (match kind with | .nat => mkConst ``CellTy.nat | .bool => mkConst ``CellTy.bool)

end Internal

end Complexity.Language.Syntax.Represented
