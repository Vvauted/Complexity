/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Continuation
import Complexity.Language.Eval.Verification
import Complexity.Language.Eval.Locals.Composition
import Complexity.Language.Eval.Locals.Continuation
import Complexity.Language.Eval.Locals.Effects
import Complexity.Language.Eval.Locals.Verification
import Complexity.Language.Eval.Locals.Captures
import Complexity.Language.Linking.Eval
import Complexity.Language.Linking.Extension
import Complexity.Language.Syntax.Imports
import Complexity.Language.Syntax.Pure
import Std.Do.WP.SimpLemmas
import Lean.Elab.Command
import Lean.Elab.Do
import Lean.Elab.PreDefinition.TerminationHint
import Lean.Meta.Closure
import Lean.Parser.Do

/-!
# Named source programs with shared buffers and allocation

`source_program P where` declares an independent typed source program from
Lean-style function headers and `do` blocks. The supported types are
`Nat`, `Bool`, `Unit`, `Buffer Nat`, `Buffer Bool`, products and `Option`, with lexical `let` and
`let mut`, assignment, named first-order calls, `if`/`then`/`else`, `while` and `return`.
Only the nearest mutable binding may be assigned; ordinary `let` bindings and
parameters are immutable. `x ← action` rebinds a mutable local to the actual
result of a supported named call, buffer read, slice or allocation. Natural arithmetic and
comparisons may be nested in bindings, assignments, return values, conditions
and call arguments. Their operands are normalized left to right into actual
lexical primitive bindings; no host
computation replaces the generated operations.

Products use ordinary pairs and `.1`/`.2` or `.fst`/`.snd` projections. Options
use `none`, `some value` and an exhaustive `match` with `none` and `some value`
branches. The payload exists only in the latter branch; leaving it preserves
the actual heap and outer mutable locals. Expected parameter, binding and
return types supply the type of `none`; otherwise give an ordinary type annotation.

A named function returning `Unit` may be called directly as a `do` statement.
Other return types require an explicit binding; results are not silently discarded.

`source_program P importing Library, Other where` additionally permits qualified
calls such as `Library.f x`. The imported programs retain their actual bodies,
including recursive calls and transitive imports, in the combined table. The
generated one-step equations use the original library observations through proved
program embeddings, so callers can reuse existing mathematical specifications.
The source handles `P.imports.Library.map` and `P.imports.Library.embedding`
expose the checked relocation for reusable contract-transfer rules, using the
library spelling in the importing clause.
Lean's persistent environment records public headers across ordinary module
imports; it does not supply an implementation or an assumed callee contract.
Compiled realization and instruction bounds remain separate proof obligations.

Each `while` has an actual source guard block, including for compound Boolean
conditions and parenthesized effectful `do` guards. The guard is reevaluated in
the current state; returning its Boolean leaves only the guard. Named loop,
guard and body observations retain complete lexical coordinates and actual
heap effects, and their equations follow from the source semantic rules.
Each named loop also exports `variant_spec`: the author supplies an invariant
and natural-valued variant over named mutable locals and the current heap.
The companion `wellFounded_spec` accepts an ordinary Lean well-founded relation
on the mutable locals and heap; it does not impose a numeric fuel or time budget.
Immutable lexical captures are fixed by generated preservation proofs, not
additional author-maintained invariant fields. This does not infer the
mathematical invariant or turn descriptor preservation into a heap frame.

Buffers expose `xs.length`, `let x ← xs.get i`, `xs.set i value` and
`let ys ← xs.slice offset length`. Reads and writes observe the current shared
heap; copying, passing or returning a buffer does not copy its contents. Buffer
parameters and results use the existing `Buffer .nat`/`Buffer .bool` Lean types.
There are no buffer literals, object-identifier constructors or host callbacks.

`let xs ← Buffer.alloc length initial` creates a fresh initialized object in the
actual source heap. The initial scalar determines its Nat or Bool element type;
both operands use the same left-to-right expression normalization as calls.
The generated core uses `Stmt.alloc`, and its monadic equation uses `Buffer.allocM`.
Allocation also supports `let mut` and rebinding an existing mutable buffer.
Even an empty allocation has a fresh identity; returning does not remove its
storage, and a later fault does not roll the heap back. Allocation is effectful
and is rejected by `source_program (pure)`. Finite target capacity and counted
initialization remain separate compilation obligations.

`with_scratch do ...` releases objects allocated inside that lexical block when
its surviving locals and return value do not refer to them. Existing-object
writes remain visible; a return still leaves the enclosing function after
cleanup. Escaping references report the source `regionEscape` fault without
releasing the heap. Named scope bodies and equations use the same source rules;
scope exit is not an implicit return-value boundary or an exception rollback.

The declaration exports `P.signatures`, `P.fId`, `P.fBody` and `P.program`,
together with the ordinary curried observation `P.f` and its equation `P.f_eq`.
The equation exposes one body using ordinary `ExceptT Fault (StateT Heap Part)` notation,
keeping named callee observations opaque. It is not a global simp rule.
`P.f_args` supplies the declared argument environment from ordinary parameters;
`P.f_contract` states a source contract with ordinary curried preconditions and
postconditions. Neither requires callers to write environment projections.
`P.f_onArgs` applies an ordinary curried predicate or bound to that environment.
`P.f_total_iff` connects those contracts to successful source evaluation without
manual environment decomposition. `P.f_spec contract` applies a supplied source
contract with the function's ordinary named arguments in a native `Std.Do` proof.
The caller can pass this specialized theorem to `mvcgen`; no callee body is
unfolded and no contract is selected or invented automatically.
The noncomputable action takes the actual
initial heap and observes `Part (Except Fault result × Heap)`; no empty heap is
supplied implicitly. It is a mathematical proof interface, not a host executable
for `#eval`.
All local signatures and imported references are collected before any new body
is translated, so forward calls and mutual recursion refer to actual entries of the
combined program. This does
not assert termination or accept arbitrary Lean functions as primitives.

Only the existing typed core is produced. Its independent execution gives
meaning to return propagation and missing returns; this module neither imports
a machine backend nor substitutes a host computation for a source operation.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

/-- One explicitly typed source parameter. -/
declare_syntax_cat sourceParameter
syntax "(" ident " : " term ")" : sourceParameter

/-- A source function uses an ordinary parsed Lean `do` body. -/
declare_syntax_cat sourceFunction
syntax "def " ident sourceParameter* " : " term " := " term
  Lean.Parser.Termination.suffix : sourceFunction

/-- Declare a finite family of named, independently interpreted source functions. -/
syntax (name := sourceProgram) "source_program " ident " where" ppLine
  many1Indent(sourceFunction) : command

/-- Declare source functions with qualified calls into previously declared source programs. -/
syntax (name := importingSourceProgram) "source_program " ident " importing " ident,+ " where" ppLine
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

-- Internal emission point: infer an equation from its checked proof instead of
-- inventing an unresolved right-hand side in a theorem header.
syntax (name := inferredSourceEquation) "source_equation% " ident " := " term : command

elab_rules : command
  | `(command| source_equation% $name:ident := $proof:term) => do
      let rawName := name.getId
      let currentNamespace ← getCurrNamespace
      let declName := if (`_root_).isPrefixOf rawName then
          rawName.replacePrefix `_root_ Name.anonymous
        else currentNamespace ++ rawName
      Lean.Elab.Command.liftTermElabM do
        let value ← Lean.Elab.Term.elabTerm proof none
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        if (← Lean.Elab.Term.logUnassignedUsingErrorInfos (← Lean.Meta.getMVars value)) then
          Lean.Elab.throwAbortTerm
        let value ← Lean.instantiateMVars value
        let type ← Lean.instantiateMVars (← Lean.Meta.inferType value)
        let closed ← Lean.Meta.Closure.mkValueTypeClosure type value false
        Lean.addDecl (.thmDecl {
          name := declName
          levelParams := closed.levelParams.toList
          type := closed.type
          value := closed.value
        })
        Lean.addDocStringCore declName
          "One source-block observation equation derived from the proved semantic composition rules."

private structure Parameter where
  name : TSyntax `ident
  type : Ty

private structure Function where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  body : TSyntax `term
  termination : TSyntax ``Lean.Parser.Termination.suffix

private structure Callee where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  id : TSyntax `ident
  observation : TSyntax `ident
  fold : TSyntax `ident
  native : Option (TSyntax `ident) := none

private structure ImportedProgram where
  name : TSyntax `ident
  family : Name
  functions : Array FunctionInfo

private structure ImportEmbedding where
  source : ImportedProgram
  map : TSyntax `term
  proof : TSyntax `term

private structure ImportDeclarations where
  declarations : Array Syntax
  program : TSyntax `term
  signatures : TSyntax `term
  embeddings : Array ImportEmbedding

private structure Binding where
  name : Option Name
  proofName : TSyntax `ident
  type : Ty
  isMutable : Bool

private abbrev Scope := List Binding

private structure Atomic where
  type : Ty
  term : TSyntax `term
  value : TSyntax `term

private structure Primitive where
  type : Ty
  term : TSyntax `term
  atom : Option (TSyntax `term)
  value : TSyntax `term

private structure BlockSite where
  name : TSyntax `ident
  scope : Scope
  result : Ty
  guard : Option (TSyntax `term)
  body : TSyntax `term

private structure LoweredBlock where
  term : TSyntax `term
  proofBody : Array (TSyntax `doElem)
  fallsThrough : Bool
  sites : Array BlockSite

private structure NormalizedValue where
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

private def typeName : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .buffer .nat => "Buffer Nat"
  | .buffer .bool => "Buffer Bool"
  | .prod left right => s!"({typeName left} × {typeName right})"
  | .option value => s!"Option ({typeName value})"

private partial def parseType (stx : TSyntax `term) : MacroM Ty := do
  match stx with
  | `(($type:term)) => parseType type
  | `(Nat) => return .nat
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | `(Buffer Nat) => return .buffer .nat
  | `(Buffer Bool) => return .buffer .bool
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.nat) => return .buffer .nat
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.bool) => return .buffer .bool
  | `($left × $right) | `(Prod $left $right) =>
      return .prod (← parseType left) (← parseType right)
  | `(Option $value) => return .option (← parseType value)
  | _ =>
      Macro.throwErrorAt stx
        "supported source types are Nat, Bool, Unit, Buffer Nat, Buffer Bool, products and Option"

private def typeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Complexity.Language.Ty.nat)
  | .bool => `(Complexity.Language.Ty.bool)
  | .unit => `(Complexity.Language.Ty.unit)
  | .buffer .nat => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.bool)
  | .prod left right => do
      `(Complexity.Language.Ty.prod $(← typeTerm left) $(← typeTerm right))
  | .option value => do
      `(Complexity.Language.Ty.option $(← typeTerm value))

private def valueTypeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .buffer .nat => `(Complexity.Language.Buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Buffer Complexity.Language.CellTy.bool)
  | .prod left right => do
      `($(← valueTypeTerm left) × $(← valueTypeTerm right))
  | .option value => do
      `(Option $(← valueTypeTerm value))

private def expectType (stx : Syntax) (actual expected : Ty) : MacroM Unit := do
  unless actual == expected do
    Macro.throwErrorAt stx s!"expected source type {typeName expected}, found {typeName actual}"

private def parameterTypes (params : Array Parameter) : MacroM (TSyntax `term) := do
  let types ← params.mapM fun param => typeTerm param.type
  `([$types,*])

private def generatedName (family : TSyntax `ident) (fn : TSyntax `ident)
    (suffix : String) : TSyntax `ident :=
  mkIdentFrom fn (family.getId ++ Name.mkSimple (fn.getId.toString ++ suffix))

private def actionName (family fn : TSyntax `ident) (pureMode : Bool) : TSyntax `ident :=
  generatedName family fn (if pureMode then "_action" else "")

private def freshProofName (ref : Syntax) (name : Name) : MacroM (TSyntax `ident) :=
  withFreshMacroScope do
    return mkIdentFrom ref (← Macro.addMacroScope name)

private def loopMember (site : BlockSite) (name : String) : TSyntax `ident :=
  mkIdentFrom site.name (site.name.getId ++ Name.mkSimple name)

private def namedSimpArgs (names : Array (TSyntax `ident)) :
    MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  names.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)

private def constantSimpArgs (names : Array Name) :
    MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  namedSimpArgs (names.map mkCIdent)

private def viewSimpArgs : MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  constantSimpArgs #[``Equiv.trans_apply, ``Equiv.symm_trans_apply, ``Equiv.prodCongr_apply,
    ``Equiv.prodCongr_symm, ``Equiv.refl_apply, ``Equiv.refl_symm, ``Equiv.symm_symm, ``Prod.map,
    ``Equiv.coe_fn_mk, ``Equiv.toFun_as_coe, ``Equiv.invFun_as_coe,
    ``Complexity.Language.Env.equivProd_apply, ``Complexity.Language.Env.equivProd_symm_apply,
    ``Complexity.Language.Env.equivUnit_apply, ``Complexity.Language.Env.equivUnit_symm_apply,
    ``Complexity.Language.Env.head, ``Complexity.Language.Env.get_tail]

private def valueSimpArgs : MacroM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  constantSimpArgs #[``Complexity.Language.Atom.eval, ``Complexity.Language.Prim.eval,
    ``Complexity.Language.Args.eval, ``Complexity.Language.CellTy.toValue,
    ``Complexity.Language.CellTy.ofValue, ``Complexity.Language.Env.cons_here,
    ``Complexity.Language.Env.cons_there, ``Complexity.Language.Env.head_cons,
    ``Complexity.Language.Env.tail_cons, ``Complexity.Language.Env.get_tail,
    ``Complexity.Language.Env.get_equivProd_symm,
    ``Complexity.Language.Env.set_here, ``Complexity.Language.Env.set_there, ``pure_bind]

private def scopeTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let types ← scope.toArray.mapM fun binding => typeTerm binding.type
  `([$types,*])

private def scopeTuple (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(())
  for binding in scope.reverse do
    values ← `(($(binding.proofName):ident, $values))
  return values

private def scopeValueTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(Unit)
  for binding in scope.reverse do
    values ← `($(← valueTypeTerm binding.type) × $values)
  return values

private def scopeView (scope : Scope) : MacroM (TSyntax `term) := do
  let mut view ← `(Complexity.Language.Env.equivUnit)
  for _ in scope.reverse do
    view ← `(Complexity.Language.Env.equivProd.trans
      (Equiv.prodCongr (Equiv.refl _) $view))
  return view

private def tupleFields (scope : Scope) (tuple : TSyntax `term) : MacroM (Array (TSyntax `term)) := do
  let mut current := tuple
  let mut fields := #[]
  for _ in scope do
    fields := fields.push (← `(($current).1))
    current ← `(($current).2)
  return fields

private def fieldsTuple (fields : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut tuple ← `(())
  for field in fields.reverse do
    tuple ← `(($field, $tuple))
  return tuple

private def tupleExtProof (scope : Scope) : MacroM (TSyntax `term) := do
  let mut proof ← `(Subsingleton.elim _ _)
  for _ in scope do
    proof ← `(Prod.ext rfl $proof)
  return proof

private def splitScopeFields (scope : Scope) (fields : Array (TSyntax `term)) :
    Array (TSyntax `term) × Array (TSyntax `term) :=
  scope.toArray.zip fields |>.foldl (fun (mutable, captured) (binding, value) =>
    if binding.isMutable then (mutable.push value, captured) else (mutable, captured.push value)) (#[], #[])

private def mergeScopeFields (scope : Scope) (mutable captured : Array (TSyntax `term)) :
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

private def freshMutableScope (site : BlockSite) (scopePrefix : String) : MacroM Scope :=
  site.scope.mapM fun binding => do
    if !binding.isMutable then return binding
    let name := Name.mkSimple (scopePrefix ++ binding.proofName.getId.eraseMacroScopes.toString)
    return { binding with proofName := ← freshProofName site.name name }

private def bindMutableFields (scope : Scope) (tuple body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let fields ← tupleFields scope tuple
  let mut result := body
  for (binding, index) in scope.zipIdx.reverse do
    if binding.isMutable then
      result ← `(let $(binding.proofName):ident := $(fields[index]!); $result)
  return result

private def mutableApplication (scope : Scope) (name : TSyntax `ident) (heap : TSyntax `term)
    (leading : Array (TSyntax `term) := #[]) : TSyntax `term :=
  Lean.Syntax.mkApp ⟨name.raw⟩ (leading ++
    (scope.toArray.filter (·.isMutable)).map (fun binding => ⟨binding.proofName.raw⟩) ++ #[heap])

private def curryScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(fun ($(binding.proofName):ident : $(← valueTypeTerm binding.type)) => $result)
  return result

private def quantifyScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(∀ ($(binding.proofName):ident : $(← valueTypeTerm binding.type)), $result)
  return result

private def scopeApplication (scope : Scope) (name : TSyntax `ident) : TSyntax `term :=
  Lean.Syntax.mkApp ⟨name.raw⟩ (scope.toArray.map fun binding => ⟨binding.proofName.raw⟩)

private def tupleApplication (scope : Scope) (name : TSyntax `ident) (tuple : TSyntax `term) :
    MacroM (TSyntax `term) := do
  return Lean.Syntax.mkApp ⟨name.raw⟩ (← tupleFields scope tuple)

private def parseFunction (stx : TSyntax `sourceFunction) : MacroM Function := do
  match stx with
  | `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term
      $termination:suffix) =>
      let mut params : Array Parameter := #[]
      for parameter in parameters do
        match parameter with
        | `(sourceParameter| ($param:ident : $type:term)) =>
            if params.any (fun previous => previous.name.getId == param.getId) then
              Macro.throwErrorAt param "duplicate source parameter name"
            params := params.push ⟨param, ← parseType type⟩
        | _ => Macro.throwErrorAt parameter "expected a source parameter '(name : type)'"
      return ⟨name, params, ← parseType result, body, termination⟩
  | _ => Macro.throwErrorAt stx "expected 'def name (argument : type) : type := do ...'"

private def variableTerm (index : Nat) : MacroM (TSyntax `term) := do
  let mut result ← `(Complexity.Language.Var.here)
  for _ in [:index] do
    result ← `(Complexity.Language.Var.there $result)
  return result

private def lookupBinding (scope : Scope) (name : TSyntax `ident) : MacroM (Binding × Nat) := do
  for (binding, index) in scope.zipIdx do
    if binding.name == some name.getId then
      return (binding, index)
  Macro.throwErrorAt name s!"unknown source variable '{name.getId}'"

private def lookupVariable (scope : Scope) (name : TSyntax `ident) : MacroM Atomic := do
  let (binding, index) ← lookupBinding scope name
  return ⟨binding.type, ← `(Complexity.Language.Atom.var $(← variableTerm index)),
    ← `($(binding.proofName):ident)⟩

private partial def parseAtom (scope : Scope) (stx : TSyntax `term) : MacroM Atomic := do
  match stx with
  | `(($value:term : $type:term)) =>
      let atom ← parseAtom scope value
      expectType type atom.type (← parseType type)
      return atom
  | `(($value:term)) => parseAtom scope value
  | `(true) => return ⟨.bool, ← `(Complexity.Language.Atom.bool true), ← `(true)⟩
  | `(false) => return ⟨.bool, ← `(Complexity.Language.Atom.bool false), ← `(false)⟩
  | `(()) => return ⟨.unit, ← `(Complexity.Language.Atom.unit), ← `(())⟩
  | `($value:num) =>
      return ⟨.nat, ← `(Complexity.Language.Atom.nat $value:num), ← `(($value:num : Nat))⟩
  | `($name:ident) => lookupVariable scope name
  | _ =>
      Macro.throwErrorAt stx
        "expected a source variable or scalar literal; name a compound operand with 'let' first"

-- Lean parses `xs.length` as a dotted identifier and `(xs).length` as a
-- projection. Both refer to the same lexical receiver, not a host declaration.
private def fieldAccess? (stx : TSyntax `term) : Option (TSyntax `term × Name) :=
  match stx with
  | `($(receiver).$field:fieldIdx) =>
      match field.raw.isFieldIdx? with
      | some 1 => some (receiver, `fst)
      | some 2 => some (receiver, `snd)
      | _ => none
  | `($receiver.$field:ident) => some (receiver, field.getId)
  | `($name:ident) =>
      match name.getId with
      | .str receiver field =>
          if receiver.isAnonymous then none
          else some (⟨(mkIdentFrom name receiver).raw⟩, Name.mkSimple field)
      | _ => none
  | _ => none

private def parseBuffer (scope : Scope) (stx : TSyntax `term) : MacroM (CellTy × Atomic) := do
  let buffer ← parseAtom scope stx
  match buffer.type with
  | .buffer kind => return (kind, buffer)
  | _ => Macro.throwErrorAt stx s!"expected a source buffer, found {typeName buffer.type}"

private def binaryPrimitive (scope : Scope) (left right : TSyntax `term)
    (result : Ty) (constructor native : Name) : MacroM Primitive := do
  let lhs ← parseAtom scope left
  let rhs ← parseAtom scope right
  expectType left lhs.type .nat
  expectType right rhs.type .nat
  let op := mkCIdent constructor
  let nativeApp := Lean.Syntax.mkCApp native #[lhs.value, rhs.value]
  let value ← if result == .bool then `(decide $nativeApp) else pure nativeApp
  return ⟨result, ← `($op $(lhs.term) $(rhs.term)), none, value⟩

private partial def parsePrimitive (scope : Scope) (stx : TSyntax `term)
    (expected : Option Ty := none) : MacroM Primitive := do
  if let some (receiver, field) := fieldAccess? stx then
    if field == `length then
      let (_, buffer) ← parseBuffer scope receiver
      return ⟨.nat, ← `(Complexity.Language.Prim.length $(buffer.term)), none,
        ← `(Complexity.Language.Buffer.length $(buffer.value))⟩
    if field == `fst || field == `snd then
      let pair ← parseAtom scope receiver
      let .prod left right := pair.type
        | Macro.throwErrorAt receiver "a product projection requires a source pair"
      if field == `fst then
        return ⟨left, ← `(Complexity.Language.Prim.fst $(pair.term)), none,
          ← `(Prod.fst $(pair.value))⟩
      else
        return ⟨right, ← `(Complexity.Language.Prim.snd $(pair.term)), none,
          ← `(Prod.snd $(pair.value))⟩
  match stx with
  | `(($value:term : $type:term)) =>
      let type ← parseType type
      let value ← parsePrimitive scope value (some type)
      expectType stx value.type type
      return value
  | `(($value:term)) => parsePrimitive scope value expected
  | `(($left, $right)) | `(Prod.mk $left $right) =>
      let lhs ← parseAtom scope left
      let rhs ← parseAtom scope right
      return ⟨.prod lhs.type rhs.type,
        ← `(Complexity.Language.Prim.pair $(lhs.term) $(rhs.term)), none,
        ← `(($(lhs.value), $(rhs.value)))⟩
  | `(Prod.fst $value) => parsePrimitive scope (← `(($value).1)) expected
  | `(Prod.snd $value) => parsePrimitive scope (← `(($value).2)) expected
  | `(none) | `(Option.none) | `(.none) =>
      let some (.option payload) := expected
        | Macro.throwErrorAt stx "the type of none needs an Option result, parameter or binding annotation"
      return ⟨.option payload, ← `(Complexity.Language.Prim.none $(← typeTerm payload)), none,
        ← `((none : Option $(← valueTypeTerm payload)))⟩
  | `(some $value) | `(Option.some $value) | `(.some $value) =>
      let payload ← parseAtom scope value
      return ⟨.option payload.type, ← `(Complexity.Language.Prim.some $(payload.term)), none,
        ← `(some $(payload.value))⟩
  | `($left + $right) => binaryPrimitive scope left right .nat ``Prim.add ``Nat.add
  | `($left * $right) => binaryPrimitive scope left right .nat ``Prim.mul ``Nat.mul
  | `($left - $right) => binaryPrimitive scope left right .nat ``Prim.sub ``Nat.sub
  | `($left / $right) => binaryPrimitive scope left right .nat ``Prim.div ``Nat.div
  | `($left % $right) => binaryPrimitive scope left right .nat ``Prim.mod ``Nat.mod
  | `($left == $right) => binaryPrimitive scope left right .bool ``Prim.eq ``Eq
  | `($left = $right) => binaryPrimitive scope left right .bool ``Prim.eq ``Eq
  | `($left < $right) => binaryPrimitive scope left right .bool ``Prim.lt ``LT.lt
  | `($left ≤ $right) => binaryPrimitive scope left right .bool ``Prim.le ``LE.le
  | `($left <= $right) => binaryPrimitive scope left right .bool ``Prim.le ``LE.le
  | _ =>
      let atom ← parseAtom scope stx
      return ⟨atom.type, ← `(Complexity.Language.Prim.atom $(atom.term)), some atom.term,
        atom.value⟩

private def checkAnnotation (annotation : Option (TSyntax `term)) (actual : Ty) : MacroM Unit := do
  if let some annotation := annotation then
    expectType annotation actual (← parseType annotation)

private def lookupFunction (functions : Array Callee) (name : TSyntax `ident) : MacroM Callee := do
  let some fn := functions.find? (fun fn => fn.name.getId == name.getId)
    | Macro.throwErrorAt name s!"unknown source function '{name.getId}'; name a local function or a qualified imported function"
  return fn

private def parseBinding (functions : Array Callee)
    (scope : Scope) (stx : TSyntax `term) :
    MacroM (Ty × TSyntax `term × TSyntax `term) := do
  if let `($head:term $operands:term*) := stx then
    if head.raw.getId == `Buffer.alloc &&
        !functions.any (fun fn => fn.name.getId == head.raw.getId) then
      unless operands.size == 2 do
        Macro.throwErrorAt stx "buffer allocation expects a length and an initial scalar"
      let length ← parseAtom scope operands[0]!
      let initial ← parseAtom scope operands[1]!
      expectType operands[0]! length.type .nat
      let kind : CellTy ← match initial.type with
        | .nat => pure CellTy.nat
        | .bool => pure CellTy.bool
        | _ => Macro.throwErrorAt operands[1]! "buffer allocation requires a Nat or Bool initial scalar"
      let kindTerm ← match kind with
        | CellTy.nat => `(Complexity.Language.CellTy.nat)
        | CellTy.bool => `(Complexity.Language.CellTy.bool)
      let allocate := mkCIdent ``Complexity.Language.Stmt.alloc
      return (Ty.buffer kind,
        ← `($allocate:ident (kind := $kindTerm) $(length.term) $(initial.term)),
        ← `(Complexity.Language.Buffer.allocM (kind := $kindTerm)
          $(length.value) $(initial.value)))
    if let some (receiver, field) := fieldAccess? head then
      if (field == `get || field == `slice) &&
          !functions.any (fun fn => fn.name.getId == head.raw.getId) then
        let (kind, buffer) ← parseBuffer scope receiver
        if field == `get then
          unless operands.size == 1 do
            Macro.throwErrorAt stx "a buffer read expects one index"
          let index ← parseAtom scope operands[0]!
          expectType operands[0]! index.type .nat
          return (kind.toTy,
            ← `(Complexity.Language.Stmt.read $(buffer.term) $(index.term)),
            ← `(Complexity.Language.Buffer.readM $(buffer.value) $(index.value)))
        else
          unless operands.size == 2 do
            Macro.throwErrorAt stx "a buffer slice expects an offset and a length"
          let offset ← parseAtom scope operands[0]!
          let length ← parseAtom scope operands[1]!
          expectType operands[0]! offset.type .nat
          expectType operands[1]! length.type .nat
          return (.buffer kind,
            ← `(Complexity.Language.Stmt.slice $(buffer.term) $(offset.term) $(length.term)),
            ← `(Complexity.Language.Buffer.sliceM $(buffer.value) $(offset.value) $(length.value)))
  let (name, operands) ← match stx with
    | `($name:ident $operands:term*) => pure (name, operands)
    | `($name:ident) => pure (name, #[])
    | _ => Macro.throwErrorAt stx "expected a named source call 'function argument ...'"
  let fn ← lookupFunction functions name
  unless operands.size == fn.params.size do
    Macro.throwErrorAt stx s!"source function '{name.getId}' expects {fn.params.size} arguments, found {operands.size}"
  let mut atoms : Array (TSyntax `term) := #[]
  let mut values : Array (TSyntax `term) := #[]
  for operand in operands, param in fn.params do
    let atom ← parseAtom scope operand
    expectType operand atom.type param.type
    atoms := atoms.push atom.term
    values := values.push atom.value
  let mut args ← `(Complexity.Language.Args.nil)
  for atom in atoms.reverse do
    args ← `(Complexity.Language.Args.cons $atom $args)
  return (fn.result, ← `(Complexity.Language.Stmt.call $(fn.id):ident $args),
    Lean.Syntax.mkApp ⟨fn.observation.raw⟩ values)

private def writeCode (scope : Scope) (stx : TSyntax `term) : MacroM LoweredBlock := do
  let `($head:term $operands:term*) := stx
    | Macro.throwErrorAt stx "expected a buffer write 'buffer.set index value'"
  let some (receiver, field) := fieldAccess? head
    | Macro.throwErrorAt stx "expected a buffer write 'buffer.set index value'"
  unless field == `set do
    Macro.throwErrorAt head "only buffer.set is supported as a standalone source action"
  let (kind, buffer) ← parseBuffer scope receiver
  unless operands.size == 2 do
    Macro.throwErrorAt stx "a buffer write expects an index and a value"
  let index ← parseAtom scope operands[0]!
  let value ← parseAtom scope operands[1]!
  expectType operands[0]! index.type .nat
  expectType operands[1]! value.type kind.toTy
  return ⟨← `(Complexity.Language.Stmt.write $(buffer.term) $(index.term) $(value.term)),
    #[← `(doElem| Complexity.Language.Buffer.writeM $(buffer.value) $(index.value) $(value.value))],
    true, #[]⟩

private def actionCode (functions : Array Callee)
    (scope : Scope) (action : TSyntax `term) : MacroM LoweredBlock := do
  if let `($head:term $_operands:term*) := action then
    if let some (_, field) := fieldAccess? head then
      if field == `set && !functions.any (fun fn => fn.name.getId == head.raw.getId) then
        return ← writeCode scope action
  let (resultType, statement, invocation) ← parseBinding functions scope action
  unless resultType == .unit do
    Macro.throwErrorAt action
      "a standalone source call must return Unit; bind its result with 'let name ← ...'"
  -- The callee's Unit result has only this empty lexical scope. The existing
  -- call boundary retains the actual final heap before the next statement.
  return ⟨← `($statement Complexity.Language.Stmt.skip),
    #[← `(doElem| $invocation:term)], true, #[]⟩

private def assignCode (scope : Scope) (name : TSyntax `ident) (value : TSyntax `term) :
    MacroM LoweredBlock := do
  -- The normalizer has already introduced every RHS temporary into this scope.
  -- Looking up the target here therefore uses its actual, possibly lifted index.
  let (binding, index) ← lookupBinding scope name
  unless binding.isMutable do
    Macro.throwErrorAt name s!"source variable '{name.getId}' is immutable; declare it with 'let mut'"
  let parsed ← parsePrimitive scope value (some binding.type)
  expectType value parsed.type binding.type
  return ⟨← `(Complexity.Language.Stmt.assign $(← variableTerm index) $(parsed.term)),
    #[← `(doElem| $(binding.proofName):ident := $(parsed.value))], true, #[]⟩

private def assignBindingCode (functions : Array Callee)
    (scope : Scope) (name : TSyntax `ident) (action : TSyntax `term) : MacroM LoweredBlock := do
  let (binding, index) ← lookupBinding scope name
  unless binding.isMutable do
    Macro.throwErrorAt name s!"source variable '{name.getId}' is immutable; declare it with 'let mut'"
  let (resultType, statement, invocation) ← parseBinding functions scope action
  expectType action resultType binding.type
  -- The action's fresh result is innermost only for this assignment. Leaving
  -- that scope drops the result slot, retaining the updated outer binding.
  let assignment ← `(Complexity.Language.Stmt.assign
    (Complexity.Language.Var.there $(← variableTerm index))
    (Complexity.Language.Prim.atom (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨← `($statement $assignment),
    #[← `(doElem| $(binding.proofName):ident ← $invocation:term)], true, #[]⟩

private def returnCode (scope : Scope) (result : Ty) (value : TSyntax `term) :
    MacroM LoweredBlock := do
  let parsed ← parsePrimitive scope value (some result)
  expectType value parsed.type result
  let term ← match parsed.atom with
    | some atom => `(Complexity.Language.Stmt.ret $atom)
    | none =>
        `(Complexity.Language.Stmt.letPrim $(parsed.term)
          (Complexity.Language.Stmt.ret (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨term, #[← `(doElem| return $(parsed.value))], false, #[]⟩

private def doSequence (elements : Array (TSyntax `doElem)) : TSyntax ``doSeq :=
  ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩

private def LoweredBlock.proofSequence (block : LoweredBlock) (normal : TSyntax `doElem) :
    TSyntax ``doSeq :=
  doSequence (if block.fallsThrough then block.proofBody.push normal else block.proofBody)

private def loopProofBody (site : BlockSite) : MacroM (Array (TSyntax `doElem)) := do
  let control ← freshProofName site.name `loopControl
  let locals ← freshProofName site.name `loopLocals
  let value ← freshProofName site.name `returned
  let error ← freshProofName site.name `error
  let invocation := scopeApplication site.scope site.name
  let mut elements := #[← `(doElem|
    let ($control:ident, $locals:ident) ← ExceptT.lift $invocation),
    ← `(doElem| match $control:ident with
      | .normal => pure ()
      | .returned $value:ident => return $value:ident
      | .fault $error:ident => throw $error:ident)]
  let fields ← tupleFields site.scope ⟨locals.raw⟩
  for binding in site.scope, field in fields do
    if binding.isMutable then
      elements := elements.push (← `(doElem| $(binding.proofName):ident := $field))
  return elements

private partial def guardElements (condition : TSyntax `term) : MacroM (List (TSyntax `doElem)) :=
  match condition with
  | `(($inner:term)) => guardElements inner
  | `(do $body:doSeq) => pure (getDoElems body).toList
  | _ => do return [← `(doElem| return $condition)]

-- Normalize only the supported expression vocabulary. Fresh lexical names are
-- consumed by the ordinary typed translator and cannot capture user bindings.
private partial def normalizeValue (stx : TSyntax `term) (atomize : Bool)
    (expected : Option Ty := none) :
    MacroM NormalizedValue := withRef stx do
  let binary (left right : TSyntax `term)
      (rebuild : TSyntax `term → TSyntax `term → MacroM (TSyntax `term))
      (leftType rightType : Option Ty := none) := do
    let lhs ← normalizeValue left true leftType
    let rhs ← normalizeValue right true rightType
    return (⟨lhs.bindings ++ rhs.bindings, ← rebuild lhs.value rhs.value, false⟩ : NormalizedValue)
  let unary (value : TSyntax `term)
      (rebuild : TSyntax `term → MacroM (TSyntax `term))
      (valueType : Option Ty := none) := do
    let value ← normalizeValue value true valueType
    return (⟨value.bindings, ← rebuild value.value, false⟩ : NormalizedValue)
  let normalized ← (match stx with
    | `(($value:term : $type:term)) => do
        let value ← normalizeValue value false (some (← parseType type))
        return { value with value := ← `(($(value.value) : $type)) }
    | `(($value:term)) => normalizeValue value false expected
    | `(($left, $right)) | `(Prod.mk $left $right) =>
        let (leftType, rightType) := match expected with
          | some (.prod left right) => (some left, some right)
          | _ => (none, none)
        binary left right (fun a b => `(($a, $b))) leftType rightType
    | `(some $value) | `(Option.some $value) | `(.some $value) =>
        let valueType := match expected with
          | some (.option payload) => some payload
          | _ => none
        unary value (fun value => `(some $value)) valueType
    | `(none) | `(Option.none) | `(.none) => pure ⟨#[], stx, false⟩
    | `(Prod.fst $value) => unary value fun value => `(Prod.fst $value)
    | `(Prod.snd $value) => unary value fun value => `(Prod.snd $value)
    | `($left + $right) => binary left right fun a b => `($a + $b)
    | `($left * $right) => binary left right fun a b => `($a * $b)
    | `($left - $right) => binary left right fun a b => `($a - $b)
    | `($left / $right) => binary left right fun a b => `($a / $b)
    | `($left % $right) => binary left right fun a b => `($a % $b)
    | `($left == $right) => binary left right fun a b => `($a == $b)
    | `($left = $right) => binary left right fun a b => `($a = $b)
    | `($left < $right) => binary left right fun a b => `($a < $b)
    | `($left ≤ $right) => binary left right fun a b => `($a ≤ $b)
    | `($left <= $right) => binary left right fun a b => `($a <= $b)
    | _ => do
        if let some (receiver, field) := fieldAccess? stx then
          if field == `length || field == `fst || field == `snd then
            return ← unary receiver fun value => `($value.$(mkIdent field):ident)
        return ⟨#[], stx, true⟩)
  if atomize && !normalized.atomic then
    let name ← freshProofName stx `operand
    let annotation ← expected.mapM valueTypeTerm
    let binding ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value))
    return ⟨normalized.bindings.push binding, ⟨name.raw⟩, true⟩
  else
    return normalized

private def normalizeCall (functions : Array Callee) (stx : TSyntax `term) :
    MacroM (Array (TSyntax `doElem) × TSyntax `term) := withRef stx do
  match stx with
  | `($head:term $operands:term*) =>
      let mut bindings := #[]
      let mut arguments := #[]
      let callee := functions.find? (fun fn => fn.name.getId == head.raw.getId)
      let mut head := head
      if callee.isNone then
        if let some (receiver, field) := fieldAccess? head then
          if field == `get || field == `set || field == `slice then
            let normalized ← normalizeValue receiver true
            bindings := normalized.bindings
            head ← `($(normalized.value).$(mkIdent field):ident)
      for operand in operands, index in [:operands.size] do
        let expected := callee.bind fun fn => fn.params[index]?.map (·.type)
        let normalized ← normalizeValue operand true expected
        bindings := bindings ++ normalized.bindings
        arguments := arguments.push normalized.value
      return (bindings, Lean.Syntax.mkApp head arguments)
  | _ => return (#[], stx)

private def optionMatch? (element : TSyntax `doElem) :
    Option (TSyntax `term × TSyntax `term × TSyntax ``doSeq × TSyntax `term × TSyntax ``doSeq) :=
  match element with
  | `(doElem| match $value:term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq) =>
      some (value, first, firstBody, second, secondBody)
  | _ => none

private def nonePattern (pattern : TSyntax `term) : Bool :=
  match pattern with
  | `(none) | `(Option.none) | `(.none) => true
  | _ => false

private def somePattern? (pattern : TSyntax `term) : Option (TSyntax `ident) :=
  match pattern with
  | `(some $name:ident) | `(Option.some $name:ident) | `(.some $name:ident) => some name
  | _ => none

private def normalizeElement (functions : Array Callee) (scope : Scope) (result : Ty)
    (element : TSyntax `doElem) :
    MacroM (Array (TSyntax `doElem) × TSyntax `doElem) := withRef element do
  if let some (value, first, firstBody, second, secondBody) := optionMatch? element then
    let normalized ← normalizeValue value true
    return (normalized.bindings, ← `(doElem| match $(normalized.value):term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq))
  match element with
  | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeValue value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let mut $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeValue value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions action
      return (bindings, ← `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions action
      return (bindings, ← `(doElem| let $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| $name:ident := $value:term) =>
      let (binding, _) ← lookupBinding scope name
      let normalized ← normalizeValue value false (some binding.type)
      return (normalized.bindings, ← `(doElem| $name:ident := $(normalized.value)))
  | `(doElem| $name:ident ← $action:term) =>
      let (bindings, action) ← normalizeCall functions action
      return (bindings, ← `(doElem| $name:ident ← $action:term))
  | `(doElem| return $value:term) =>
      let normalized ← normalizeValue value false (some result)
      return (normalized.bindings, ← `(doElem| return $(normalized.value)))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let normalized ← normalizeValue condition false
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| while $_condition do $_body) => return (#[], element)
  | `(doElem| with_scratch do $_body:doSeq) => return (#[], element)
  | `(doElem| $action:term) =>
      let (bindings, action) ← normalizeCall functions action
      return (bindings, ← `(doElem| $action:term))
  | _ => return (#[], element)

private def statementCode (family : TSyntax `ident) (functions : Array Callee)
    (owner : TSyntax `ident)
    (recurse : Scope → Ty → List (TSyntax `doElem) → Nat → MacroM LoweredBlock)
    (scope : Scope) (result : Ty) (element : TSyntax `doElem) (nextIndex : Nat) :
    MacroM LoweredBlock := withRef element do
  if let some (value, first, firstBody, second, secondBody) := optionMatch? element then
    let (noneBody, payload, someBody) ←
      if nonePattern first then
        match somePattern? second with
        | some payload => pure (firstBody, payload, secondBody)
        | none => Macro.throwErrorAt second "expected a 'some name' option pattern"
      else if nonePattern second then
        match somePattern? first with
        | some payload => pure (secondBody, payload, firstBody)
        | none => Macro.throwErrorAt first "expected a 'some name' option pattern"
      else Macro.throwErrorAt element "an option match needs exactly none and some branches"
    let option ← parseAtom scope value
    let .option payloadType := option.type
      | Macro.throwErrorAt value "source matching currently supports Option values"
    let payloadName ← freshProofName payload payload.getId
    let noneCode ← recurse scope result (getDoElems noneBody).toList nextIndex
    let someCode ← recurse (⟨some payload.getId, payloadName, payloadType, false⟩ :: scope)
      result (getDoElems someBody).toList (nextIndex + noneCode.sites.size)
    let normal ← `(doElem| pure ())
    let noneBody := noneCode.proofSequence normal
    let someBody := someCode.proofSequence normal
    let branch ← `(doElem| match $(option.value):term with
      | none => $noneBody:doSeq
      | some $payloadName:ident => $someBody:doSeq)
    return ⟨← `(Complexity.Language.Stmt.matchOption $(option.term)
        $(noneCode.term) $(someCode.term)),
      #[branch], noneCode.fallsThrough || someCode.fallsThrough, noneCode.sites ++ someCode.sites⟩
  match element with
  | `(doElem| $name:ident := $value:term) => assignCode scope name value
  | `(doElem| $name:ident ← $action:term) => assignBindingCode functions scope name action
  | `(doElem| return $value:term) => returnCode scope result value
  | `(doElem| return) => returnCode scope result (← `(()))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let parsed ← parsePrimitive scope condition
      expectType condition parsed.type .bool
      let saved ← freshProofName condition `condition
      let inner := if parsed.atom.isSome then scope
        else ⟨none, saved, Ty.bool, false⟩ :: scope
      let yesCode ← recurse inner result (getDoElems yes).toList nextIndex
      let noCode ← recurse inner result (getDoElems no).toList (nextIndex + yesCode.sites.size)
      let term ← match parsed.atom with
        | some atom =>
            `(Complexity.Language.Stmt.ite $atom $(yesCode.term) $(noCode.term))
        | none =>
            `(Complexity.Language.Stmt.letPrim $(parsed.term)
              (Complexity.Language.Stmt.ite
                (Complexity.Language.Atom.var Complexity.Language.Var.here)
                $(yesCode.term) $(noCode.term)))
      let normal ← `(doElem| pure ())
      let yesBody := yesCode.proofSequence normal
      let noBody := noCode.proofSequence normal
      let conditionValue ← if parsed.atom.isSome then pure parsed.value else `($saved:ident)
      let branch ← `(doElem| if $conditionValue then $yesBody:doSeq else $noBody:doSeq)
      let proofBody ← if parsed.atom.isSome then pure #[branch] else do
        let capture ← `(doElem| let $saved:ident : Bool := $(parsed.value))
        pure #[capture, branch]
      return ⟨term, proofBody, yesCode.fallsThrough || noCode.fallsThrough,
        yesCode.sites ++ noCode.sites⟩
  | `(doElem| while $condition do $body) =>
      let name := generatedName family owner s!"_loop{nextIndex}"
      let guardCode ← recurse scope .bool (← guardElements condition) (nextIndex + 1)
      let bodyCode ← recurse scope result (getDoElems body).toList
        (nextIndex + 1 + guardCode.sites.size)
      let site : BlockSite := ⟨name, scope, result, some guardCode.term, bodyCode.term⟩
      let code := loopMember site "Code"
      return ⟨⟨code.raw⟩, ← loopProofBody site, true,
        guardCode.sites ++ bodyCode.sites |>.push site⟩
  | `(doElem| with_scratch do $body:doSeq) =>
      let name := generatedName family owner s!"_scope{nextIndex}"
      let bodyCode ← recurse scope result (getDoElems body).toList (nextIndex + 1)
      let site : BlockSite := ⟨name, scope, result, none, bodyCode.term⟩
      let code := loopMember site "Code"
      -- The observation exposes Control rather than a syntactically terminal
      -- return. Retain its normal continuation just as for a named loop.
      return ⟨⟨code.raw⟩, ← loopProofBody site, true,
        bodyCode.sites.push site⟩
  | `(doElem| $action:term) => actionCode functions scope action
  | _ =>
      Macro.throwErrorAt element
        "unsupported source statement; use let, let mut, assignment, a named call, buffer access or allocation, with_scratch, if/then/else, Option match, while, or return"

private partial def blockCode (family : TSyntax `ident) (functions : Array Callee)
    (owner : TSyntax `ident) (scope : Scope) (result : Ty)
    (elements : List (TSyntax `doElem)) (nextIndex : Nat) : MacroM LoweredBlock := do
  match elements with
  | [] => return ⟨← `(Complexity.Language.Stmt.skip), #[], true, #[]⟩
  | element :: rest => withRef element do
      let (bindings, element) ← normalizeElement functions scope result element
      if !bindings.isEmpty then
        return ← blockCode family functions owner scope result
          (bindings.toList ++ element :: rest) nextIndex
      match element with
      | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value (← annotation.mapM parseType)
          checkAnnotation annotation parsed.type
          let proofName ← freshProofName name name.getId
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, true⟩ :: scope) result rest nextIndex
          let type ← valueTypeTerm parsed.type
          let binding ← `(doElem| let mut $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value (← annotation.mapM parseType)
          checkAnnotation annotation parsed.type
          let proofName ← freshProofName name name.getId
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, false⟩ :: scope) result rest nextIndex
          let type ← valueTypeTerm parsed.type
          let binding ← `(doElem| let $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, true⟩ :: scope) result rest nextIndex
          let type ← valueTypeTerm bindingType
          let binding ← `(doElem| let mut $proofName:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, false⟩ :: scope) result rest nextIndex
          let type ← valueTypeTerm bindingType
          let binding ← `(doElem| let $proofName:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | _ =>
          let statement ← statementCode family functions owner (blockCode family functions owner)
            scope result element nextIndex
          if rest.isEmpty then
            return statement
          else
            let continuation ← blockCode family functions owner scope result rest
              (nextIndex + statement.sites.size)
            return ⟨← `(Complexity.Language.Stmt.seq $(statement.term) $(continuation.term)),
              if statement.fallsThrough then statement.proofBody ++ continuation.proofBody
                else statement.proofBody,
              statement.fallsThrough && continuation.fallsThrough,
              statement.sites ++ continuation.sites⟩

private def functionCode (family : TSyntax `ident) (functions : Array Callee)
    (fn : Function) : MacroM LoweredBlock := do
  match fn.body with
  | `(do $body:doSeq) =>
      let scope : Scope := fn.params.toList.map fun param =>
        ⟨some param.name.getId, param.name, param.type, false⟩
      blockCode family functions fn.name scope fn.result (getDoElems body).toList 1
  | _ => Macro.throwErrorAt fn.body "source function bodies must be supported 'do' blocks"

private def loopCodeDeclarations (signatures : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let locals := loopMember site "Locals"
  let view := loopMember site "View"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let code := loopMember site "Code"
  let types ← scopeTypes site.scope
  let result ← typeTerm site.result
  let localsType ← scopeValueTypes site.scope
  let viewTerm ← scopeView site.scope
  let viewApply := loopMember site "view_apply"
  let viewSymmApply := loopMember site "view_symm_apply"
  let entry ← freshProofName site.name `entry
  let values ← freshProofName site.name `values
  let fields ← tupleFields site.scope ⟨values.raw⟩
  let mut projected ← `(())
  let mut restored ← `(Complexity.Language.Env.empty)
  for (binding, index) in site.scope.zipIdx.reverse do
    let sourceVar ← variableTerm index
    projected ← `((Complexity.Language.Env.get $entry:ident $sourceVar, $projected))
    let type ← typeTerm binding.type
    restored ← `(Complexity.Language.Env.cons (τ := $type) $(fields[index]!) $restored)
  let mut declarations := #[
    (← `(command| /-- Complete lexical coordinates for this source block. -/
      abbrev $locals:ident := $localsType)).raw,
    (← `(command| /-- Lossless proof coordinates, including fixed and shadowed captures. -/
      def $view:ident : Complexity.Language.Env $types ≃ $locals:ident := $viewTerm)).raw,
    (← `(command| /-- Observe lexical coordinates without unfolding the equivalence structure. -/
      theorem $viewApply:ident ($entry:ident : Complexity.Language.Env $types) :
          $view:ident $entry:ident = $projected := rfl)).raw,
    (← `(command| /-- Restore complete lexical coordinates without unfolding proof fields. -/
      theorem $viewSymmApply:ident ($values:ident : $locals:ident) :
          ($view:ident).symm $values:ident = $restored := rfl)).raw]
  if let some guardTerm := site.guard then
    declarations := declarations.push (← `(command|
      /-- The actual value-producing guard, reevaluated on every iteration. -/
      def $guard:ident : Complexity.Language.Stmt $signatures:ident $types .bool := $guardTerm)).raw
  declarations := declarations.push (← `(command|
    /-- The actual parsed lexical body, with its enclosing return type. -/
    def $body:ident : Complexity.Language.Stmt $signatures:ident $types $result := $(site.body))).raw
  let codeTerm ← match site.guard with
    | some _ => `(Complexity.Language.Stmt.while $guard:ident $body:ident)
    | none => `(Complexity.Language.Stmt.scope $body:ident)
  declarations := declarations.push (← `(command|
    /-- This actual source block, retaining its loop or allocation-scope semantics. -/
    def $code:ident : Complexity.Language.Stmt $signatures:ident $types $result := $codeTerm)).raw
  return declarations

private def loopObservationDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let localsType := loopMember site "Locals"
  let view := loopMember site "View"
  let tuple ← scopeTuple site.scope
  let mut declarations := #[]
  let observations := (if site.guard.isSome then [("guard", "Guard", Ty.bool)] else []) ++
    [("body", "Body", site.result), ("", "Code", site.result)]
  for (suffix, codeSuffix, result) in observations do
    let name := if suffix.isEmpty then site.name else loopMember site suffix
    let code := loopMember site codeSuffix
    let result ← typeTerm result
    let type ← quantifyScope site.scope
      (← `(StateT Complexity.Language.Heap Part
        (Complexity.Language.Control $result × $localsType:ident)))
    let value ← curryScope site.scope
      (← `(Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident $tuple))
    declarations := declarations.push (← `(command|
      /-- The actual source block observed with ordinary named local inputs. -/
      noncomputable def $name:ident : $type := $value)).raw
    let foldName := loopMember site (if suffix.isEmpty then "observe" else suffix ++ "_observe")
    let current ← freshProofName site.name `locals
    let applied ← tupleApplication site.scope name ⟨current.raw⟩
    declarations := declarations.push (← `(command|
      /-- Coordinate conversion for composing this named observation. -/
      theorem $foldName:ident ($current:ident : $localsType:ident) :
          Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident $current:ident =
            $applied := rfl)).raw
  return declarations

private def loopCaptureDeclarations (site : BlockSite) : MacroM (Array Syntax) := do
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutableType ← scopeValueTypes mutableScope
  let capturedType ← scopeValueTypes capturedScope
  let locals := loopMember site "Locals"
  let mutable := loopMember site "Mutable"
  let captured := loopMember site "Captured"
  let regroup := loopMember site "Regroup"
  let regroupApply := loopMember site "regroup_apply"
  let regroupSymmApply := loopMember site "regroup_symm_apply"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let captureViewApply := loopMember site "captureView_apply"
  let types ← scopeTypes site.scope
  let values ← freshProofName site.name `values
  let grouped ← freshProofName site.name `grouped
  let entry ← freshProofName site.name `entry
  let fields ← tupleFields site.scope ⟨values.raw⟩
  let (mutableFields, capturedFields) := splitScopeFields site.scope fields
  let regrouped ← `(( $(← fieldsTuple mutableFields), $(← fieldsTuple capturedFields) ))
  let mutableValues ← tupleFields mutableScope (← `(($grouped:ident).1))
  let capturedValues ← tupleFields capturedScope (← `(($grouped:ident).2))
  let restored ← fieldsTuple (mergeScopeFields site.scope mutableValues capturedValues)
  let leftProof ← tupleExtProof site.scope
  let rightProof ← `(Prod.ext $(← tupleExtProof mutableScope) $(← tupleExtProof capturedScope))
  let mut entryFields := #[]
  for (_, index) in site.scope.zipIdx do
    entryFields := entryFields.push
      (← `(Complexity.Language.Env.get $entry:ident $(← variableTerm index)))
  let (mutableEntries, capturedEntries) := splitScopeFields site.scope entryFields
  let projected ← `(( $(← fieldsTuple mutableEntries), $(← fieldsTuple capturedEntries) ))
  return #[
    (← `(command| /-- The ordinary mutable locals of this source loop. -/
      abbrev $mutable:ident := $mutableType)).raw,
    (← `(command| /-- Fixed lexical captures, independent of the shared heap. -/
      abbrev $captured:ident := $capturedType)).raw,
    (← `(command| /-- A lossless coordinate permutation; no source operation is executed. -/
      def $regroup:ident : $locals:ident ≃ ($mutable:ident × $captured:ident) where
        toFun $values:ident := $regrouped
        invFun $grouped:ident := $restored
        left_inv _ := $leftProof
        right_inv _ := $rightProof)).raw,
    (← `(command| theorem $regroupApply:ident ($values:ident : $locals:ident) :
      $regroup:ident $values:ident = $regrouped := rfl)).raw,
    (← `(command| theorem $regroupSymmApply:ident
        ($grouped:ident : $mutable:ident × $captured:ident) :
      ($regroup:ident).symm $grouped:ident = $restored := rfl)).raw,
    (← `(command| /-- The same complete environment, grouped by source mutability. -/
      def $captureView:ident : Complexity.Language.Env $types ≃
          ($mutable:ident × $captured:ident) := ($view:ident).trans $regroup:ident)).raw,
    (← `(command| theorem $captureViewApply:ident ($entry:ident : Complexity.Language.Env $types) :
      $captureView:ident $entry:ident = $projected := rfl)).raw]

private def loopCaptureFrameDeclarations (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM (Array Syntax) := do
  let types ← scopeTypes site.scope
  let captureView := loopMember site "CaptureView"
  let captureViewApply := loopMember site "captureView_apply"
  let preservedArgs ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let preservedArgs := preservedArgs ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.PreservesLocal, ``Complexity.Language.Var.index])
  let entry ← freshProofName site.name `entry
  let finish ← freshProofName site.name `finish
  let control ← freshProofName site.name `control
  let execution ← freshProofName site.name `execution
  let mut capturesProof ← `(rfl)
  for (binding, index) in site.scope.zipIdx.reverse do
    unless binding.isMutable do
      let sourceVar ← variableTerm index
      capturesProof ← `(Prod.ext
        (Complexity.Language.Exec.get_eq $execution:ident $sourceVar
          (by simp [$preservedArgs,*])) $capturesProof)
  let mut declarations := #[]
  for (suffix, codeSuffix, result) in
      [("guard_preservesCaptures", "Guard", Ty.bool), ("body_preservesCaptures", "Body", site.result)] do
    let name := loopMember site suffix
    let code := loopMember site codeSuffix
    let result ← typeTerm result
    declarations := declarations.push (← `(command|
      /-- Source lexical immutability preserves these captures on every actual exit. -/
      theorem $name:ident {$entry:ident $finish:ident : Complexity.Language.State $types}
          {$control:ident : Complexity.Language.Control $result}
          ($execution:ident : Complexity.Language.Exec $program:ident $code:ident
            $entry:ident $finish:ident $control:ident) :
          ($captureView:ident ($finish:ident).locals).2 =
            ($captureView:ident ($entry:ident).locals).2 := by
        simp only [$captureViewApply:ident]
        exact $capturesProof)).raw
  return declarations

private def loopTerminationStepType (site : BlockSite)
    (invariant progress normal returned : TSyntax `ident) (wellFoundedMode : Bool) :
    MacroM (TSyntax `term) := do
  let afterGuardScope ← freshMutableScope site "afterGuard_"
  let afterBodyScope ← freshMutableScope site "afterBody_"
  let startHeap ← freshProofName site.name `startHeap
  let currentHeap ← freshProofName site.name `currentHeap
  let guardOutcome ← freshProofName site.name `guardOutcome
  let afterGuardHeap ← freshProofName site.name `afterGuardHeap
  let bodyOutcome ← freshProofName site.name `bodyOutcome
  let afterBodyHeap ← freshProofName site.name `afterBodyHeap
  let value ← freshProofName site.name `value
  let again ← freshProofName site.name `again
  let decrease ← if wellFoundedMode then do
      let afterMutable ← scopeTuple (afterBodyScope.filter (·.isMutable))
      let beforeMutable ← scopeTuple (site.scope.filter (·.isMutable))
      `($progress:ident ($afterMutable, $afterBodyHeap:ident)
        ($beforeMutable, $startHeap:ident))
    else
      `($(mutableApplication afterBodyScope progress ⟨afterBodyHeap.raw⟩) <
        $(mutableApplication site.scope progress ⟨startHeap.raw⟩))
  let bodyNormal ← `($(mutableApplication afterBodyScope invariant ⟨afterBodyHeap.raw⟩) ∧
    $decrease)
  let bodyReturned := mutableApplication afterBodyScope returned ⟨afterBodyHeap.raw⟩ #[⟨value.raw⟩]
  let bodyPost ← `(match ($bodyOutcome:ident).1 with
    | .normal => $bodyNormal
    | .returned $value:ident => $bodyReturned
    | .fault _ => False)
  let bodyPost ← bindMutableFields afterBodyScope (← `(($bodyOutcome:ident).2)) bodyPost
  let bodyInvocation := scopeApplication afterGuardScope (loopMember site "body")
  let bodySpec ← `(Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
    $bodyInvocation (fun $currentHeap:ident => ⟨$currentHeap:ident = $afterGuardHeap:ident⟩)
    (fun $bodyOutcome:ident $afterBodyHeap:ident => ⟨$bodyPost⟩, ⟨⟩))
  let guardNormal := mutableApplication afterGuardScope normal ⟨afterGuardHeap.raw⟩
  let guardPost ← `(match ($guardOutcome:ident).1 with
    | .returned $again:ident => if $again:ident then $bodySpec else $guardNormal
    | .normal => False
    | .fault _ => False)
  let guardPost ← bindMutableFields afterGuardScope (← `(($guardOutcome:ident).2)) guardPost
  let guardInvocation := scopeApplication site.scope (loopMember site "guard")
  let step ← `(∀ ($startHeap:ident : Complexity.Language.Heap),
    $(mutableApplication site.scope invariant ⟨startHeap.raw⟩) →
    Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
      $guardInvocation (fun $currentHeap:ident => ⟨$currentHeap:ident = $startHeap:ident⟩)
      (fun $guardOutcome:ident $afterGuardHeap:ident => ⟨$guardPost⟩, ⟨⟩))
  quantifyScope (site.scope.filter (·.isMutable)) step

private def loopVariantPost (site : BlockSite) (normal returned : TSyntax `ident)
    (fullScope : Bool) : MacroM (TSyntax `term) := do
  let finishScope ← freshMutableScope site "final_"
  let finishScope := if fullScope then finishScope else finishScope.filter (·.isMutable)
  let outcome ← freshProofName site.name `outcome
  let heap ← freshProofName site.name `heap
  let value ← freshProofName site.name `value
  let normalPost := mutableApplication finishScope normal ⟨heap.raw⟩
  let returnPost := mutableApplication finishScope returned ⟨heap.raw⟩ #[⟨value.raw⟩]
  let post ← `(match ($outcome:ident).1 with
    | .normal => $normalPost
    | .returned $value:ident => $returnPost
    | .fault _ => False)
  let post ← bindMutableFields finishScope (← `(($outcome:ident).2)) post
  `((fun $outcome:ident $heap:ident => ⟨$post⟩, ⟨⟩))

private def loopTerminationDeclaration (program : TSyntax `ident) (site : BlockSite)
    (wellFoundedMode : Bool) :
    MacroM Syntax := do
  let name := loopMember site (if wellFoundedMode then "wellFounded_spec" else "variant_spec")
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutableType := loopMember site "Mutable"
  let captureView := loopMember site "CaptureView"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let invariant ← freshProofName site.name `invariant
  let progress ← freshProofName site.name (if wellFoundedMode then `relation else `variant)
  let wellFounded ← freshProofName site.name `wellFounded
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let step ← freshProofName site.name `step
  let mutable ← freshProofName site.name `mutable
  let heap ← freshProofName site.name `heap
  let initial ← freshProofName site.name `initial
  let captures ← scopeTuple capturedScope
  let initialMutable ← scopeTuple mutableScope
  let fields ← tupleFields mutableScope ⟨mutable.raw⟩
  let invApplication := Lean.Syntax.mkApp ⟨invariant.raw⟩ (fields.push ⟨heap.raw⟩)
  let rawInvariant ← `(fun ($mutable:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) => $invApplication)
  let rawProgress ← if wellFoundedMode then `($progress:ident) else do
    let application := Lean.Syntax.mkApp ⟨progress.raw⟩ (fields.push ⟨heap.raw⟩)
    `(fun ($mutable:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) => $application)
  let rawPost ← loopVariantPost site normal returned false
  let actualPost ← loopVariantPost site normal returned true
  let transportArgs ← namedSimpArgs #[captureView,
    loopMember site "regroup_apply", loopMember site "regroup_symm_apply",
    loopMember site "guard_observe", loopMember site "body_observe", loopMember site "observe"]
  let transportArgs := transportArgs ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.observe_reindex, ``Std.Do.Triple, ``Std.Do.WP.map])
  let wpArgs ← constantSimpArgs
    #[``Std.Do.WP.wp, ``Std.Do.PredTrans.pushArg, ``Part.TotalCorrectness.wp]
  let stepApplication := Lean.Syntax.mkApp ⟨step.raw⟩
    (fields ++ #[⟨heap.raw⟩, ⟨initial.raw⟩])
  let rawStep ← `(by
    intro $mutable:ident $heap:ident $initial:ident
    have checked := $stepApplication
    simp only [$transportArgs,*] at checked ⊢
    simp only [$wpArgs,*] at checked ⊢
    intro currentHeap sameHeap
    obtain ⟨⟨⟨guardControl, guardLocals⟩, guardHeap⟩, guardMember, guardPost⟩ :=
      checked currentHeap sameHeap
    refine ⟨((guardControl, guardLocals), guardHeap), guardMember, ?_⟩
    cases guardControl with
    | normal => exact guardPost
    | fault error => exact guardPost
    | returned again =>
        cases again with
        | false => exact guardPost
        | true =>
            intro currentHeap sameHeap
            obtain ⟨⟨⟨bodyControl, bodyLocals⟩, bodyHeap⟩, bodyMember, bodyPost⟩ :=
              guardPost currentHeap sameHeap
            refine ⟨((bodyControl, bodyLocals), bodyHeap), bodyMember, ?_⟩
            cases bodyControl <;> exact bodyPost)
  let invocation := scopeApplication site.scope site.name
  let finalType ← `(Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
    (ps := .arg Complexity.Language.Heap .pure) $invocation
    (fun $heap:ident => ⟨$(mutableApplication site.scope invariant ⟨heap.raw⟩)⟩) $actualPost)
  let stepType ← loopTerminationStepType site invariant progress normal returned wellFoundedMode
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let progressType ← if wellFoundedMode then
      `(($mutableType:ident × Complexity.Language.Heap) →
        ($mutableType:ident × Complexity.Language.Heap) → Prop)
    else quantifyScope mutableScope (← `(Complexity.Language.Heap → Nat))
  let result ← valueTypeTerm site.result
  let returnType ← `($result → $predicateType)
  let conclusion ← `(∀ ($normal:ident : $predicateType)
    ($returned:ident : $returnType) ($step:ident : $stepType),
      $(← quantifyScope mutableScope finalType))
  let conclusion ← if wellFoundedMode then
      `(∀ ($wellFounded:ident : WellFounded $progress:ident), $conclusion)
    else pure conclusion
  let type ← quantifyScope capturedScope (← `(∀ ($invariant:ident : $predicateType)
    ($progress:ident : $progressType), $conclusion))
  let specification ← if wellFoundedMode then
      `(Complexity.Language.Stmt.observe_while_fixed_spec
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $rawInvariant $rawProgress
        $wellFounded:ident $rawPost $rawStep $initialMutable)
    else
      `(Complexity.Language.Stmt.observe_while_fixed_variant_spec
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $rawInvariant $rawProgress $rawPost
        $rawStep $initialMutable)
  let proof ← curryScope mutableScope (← `(by
    have specification := $specification
    simp only [$transportArgs,*] at specification ⊢
    simp only [$wpArgs,*] at specification ⊢
    intro currentHeap initial
    obtain ⟨⟨⟨control, locals⟩, finalHeap⟩, member, post⟩ := specification currentHeap initial
    refine ⟨((control, locals), finalHeap), member, ?_⟩
    cases control <;> exact post))
  let proof ← `(fun $normal:ident $returned:ident $step:ident => $proof)
  let proof ← if wellFoundedMode then `(fun $wellFounded:ident => $proof) else pure proof
  let proof ← curryScope capturedScope (← `(fun $invariant:ident $progress:ident => $proof))
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Prove this actual loop with fixed captures and well-founded progress on its mutable locals.
    Only normal body exits must decrease; guard effects, returns and faults retain their real heap. -/
    theorem $name:ident : $type := $proof)).raw

private def loopEquationDeclarations (site : BlockSite) (sites : Array BlockSite)
    (calleeFolds : Array (TSyntax `ident)) : MacroM (Array Syntax) := do
  let loopCode := loopMember site "Code"
  let expandedFolds ← sites.mapM fun other => do
    return (other, ← freshProofName other.name `nestedObservation)
  let expandedFoldArgs ← namedSimpArgs (expandedFolds.map (·.2))
  let viewDefinitions ← namedSimpArgs (sites.map fun other => loopMember other "View")
  let foldNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "body_observe", loopMember other "observe"] ++
      if other.guard.isSome then #[loopMember other "guard_observe"] else #[])
  let nestedLoops ← namedSimpArgs (sites.map fun other => loopMember other "observe")
  let viewNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "view_apply", loopMember other "view_symm_apply"])
  let calleeFolds ← namedSimpArgs calleeFolds
  let compositionArgs ← constantSimpArgs #[``Complexity.Language.Stmt.observe_skip,
    ``Complexity.Language.Stmt.observe_assign, ``Complexity.Language.Stmt.observe_ret,
    ``Complexity.Language.Stmt.observe_seq, ``Complexity.Language.Stmt.observe_ite,
    ``Complexity.Language.Stmt.observe_matchOption,
    ``Complexity.Language.Stmt.observe_letPrim, ``Complexity.Language.Stmt.observe_read,
    ``Complexity.Language.Stmt.observe_write, ``Complexity.Language.Stmt.observe_slice,
    ``Complexity.Language.Stmt.observe_alloc, ``Complexity.Language.Stmt.observe_call]
  let sharedArgs := compositionArgs ++ nestedLoops ++ viewNames ++ calleeFolds ++
    (← viewSimpArgs) ++ (← valueSimpArgs)
  let mut declarations := #[]
  let observations := (if site.guard.isSome then [("guard", "Guard")] else []) ++
    [("body", "Body")]
  for (suffix, codeSuffix) in observations do
    let name := loopMember site suffix
    let equation := loopMember site (suffix ++ "_eq")
    let code := loopMember site codeSuffix
    let applied := scopeApplication site.scope name
    let allArgs := (← namedSimpArgs #[code]) ++ sharedArgs
    let mut proof ← `(by
      have equation : $applied = $applied := rfl
      conv at equation =>
        lhs
        unfold $name:ident
        simp only [$allArgs,*]
        simp (config := { failIfUnchanged := false }) only [$viewDefinitions,*]
        simp (config := { failIfUnchanged := false }) only [$expandedFoldArgs,*]
        dsimp only [Complexity.Language.Env.equivProd, Complexity.Language.Env.equivUnit,
          Equiv.symm]
        simp (config := { failIfUnchanged := false }) only
          [Equiv.coe_fn_mk, Complexity.Language.Env.cons_here,
            Complexity.Language.Env.cons_there, Complexity.Language.Env.head_cons,
            Complexity.Language.Env.tail_cons, Complexity.Language.Env.get_tail]
      exact equation.symm)
    -- Composing lexical bindings constructs a view definitionally equal to a
    -- nested block's named View. Normalize just these equation-local copies;
    -- public views stay opaque to the separate continuation and frame proofs.
    for (other, folded) in expandedFolds.reverse do
      let observed := loopMember other "observe"
      let view := loopMember other "View"
      proof ← `(by
        have $folded:ident := $observed:ident
        dsimp only [$view:ident] at $folded:ident
        exact $proof)
    let curriedProof ← curryScope site.scope proof
    declarations := declarations.push
      (← `(command| source_equation% $equation:ident := $curriedProof)).raw
  let name := site.name
  let equation := loopMember site "eq"
  let applied := scopeApplication site.scope name
  let composition := mkCIdent (if site.guard.isSome then
    ``Complexity.Language.Stmt.observe_while else ``Complexity.Language.Stmt.observe_scope)
  let proof ← curryScope site.scope (← `(by
    have equation : $applied = $applied := rfl
    conv at equation =>
      lhs
      unfold $name:ident
      rw [$loopCode:ident, $composition:ident]
      simp only [$foldNames,*]
    exact equation.symm))
  declarations := declarations.push (← `(command| source_equation% $equation:ident := $proof)).raw
  return declarations

private def loopContinuationDeclaration (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM Syntax := do
  let name := loopMember site "continue_eq"
  let view := loopMember site "View"
  let code := loopMember site "Code"
  let types ← scopeTypes site.scope
  let result ← valueTypeTerm site.result
  let entry ← freshProofName site.name `entry
  let next ← freshProofName site.name `next
  let control ← freshProofName site.name `control
  let locals ← freshProofName site.name `locals
  let value ← freshProofName site.name `value
  let error ← freshProofName site.name `error
  let execution ← freshProofName site.name `execution
  let initialHeap ← freshProofName site.name `initialHeap
  let finalHeap ← freshProofName site.name `finalHeap
  let input ← `($view:ident $entry:ident)
  let invocation ← tupleApplication site.scope site.name input
  let fields ← tupleFields site.scope ⟨locals.raw⟩
  let mut restored ← `(Complexity.Language.Env.empty)
  let mut captures : Array (TSyntax `ident × TSyntax `term) := #[]
  for (binding, index) in site.scope.zipIdx.reverse do
    let sourceVar ← variableTerm index
    let field ← if binding.isMutable then pure fields[index]! else
      `(Complexity.Language.Env.get $entry:ident $sourceVar)
    let type ← typeTerm binding.type
    restored ← `(Complexity.Language.Env.cons (τ := $type) $field $restored)
    unless binding.isMutable do
      captures := captures.push (← freshProofName site.name `capture, sourceVar)
  let captureNames ← namedSimpArgs (captures.map (·.1))
  let viewNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "view_apply", loopMember other "view_symm_apply"])
  let codeNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let viewArgs := viewNames ++ (← viewSimpArgs)
  let normalArgs := viewArgs ++ captureNames
  let preservedArgs := codeNames ++
    (← constantSimpArgs #[``Complexity.Language.Stmt.PreservesLocal,
      ``Complexity.Language.Var.index])
  let captureArgs := (← constantSimpArgs #[``Equiv.symm_apply_apply]) ++ viewArgs ++
    (← constantSimpArgs #[``Complexity.Language.Env.cons_here, ``Complexity.Language.Env.cons_there])
  let mut normalProof ← `(by
    simp only [$normalArgs,*])
  for (capture, sourceVar) in captures.reverse do
    normalProof ← `(by
      have $capture:ident := Complexity.Language.Exec.get_eq $execution:ident $sourceVar
        (by simp [$preservedArgs,*])
      simp only [$captureArgs,*] at $capture:ident
      exact $normalProof)
  let declaration ← `(command|
    /-- Resume from actual mutable locals; immutable captures are preserved by the source frame. -/
    theorem $name:ident ($entry:ident : Complexity.Language.Env $types)
        ($next:ident : Complexity.Language.Env $types →
          ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part) $result) :
        Complexity.Language.Stmt.evalWith $code:ident $program:ident $entry:ident $next:ident = (do
          let ($control:ident, $locals:ident) ← ExceptT.lift $invocation
          match $control:ident with
          | .normal => $next:ident $restored
          | .returned $value:ident => pure $value:ident
          | .fault $error:ident => throw $error:ident) := by
      rw [Complexity.Language.Stmt.evalWith_eq_observe $view:ident]
      apply Complexity.Language.Stmt.observe_bind_congr_except
        $view:ident $code:ident $program:ident ($view:ident $entry:ident)
      intro $initialHeap:ident $finalHeap:ident $control:ident $locals:ident $execution:ident
      cases $control:ident with
      | normal => exact $normalProof
      | returned value => rfl
      | fault error => rfl)
  return declaration.raw

private def scopeSpecificationDeclaration (program : TSyntax `ident) (site : BlockSite) :
    MacroM Syntax := do
  let name := loopMember site "spec"
  let localsType := loopMember site "Locals"
  let view := loopMember site "View"
  let body := loopMember site "Body"
  let result ← typeTerm site.result
  let tuple ← scopeTuple site.scope
  let invocation := scopeApplication site.scope site.name
  let bodyInvocation := scopeApplication site.scope (loopMember site "body")
  let post ← freshProofName site.name `post
  let heap ← freshProofName site.name `heap
  let outcome ← freshProofName site.name `outcome
  let finish ← freshProofName site.name `finish
  let postType ← `(Std.Do.PostCond (Complexity.Language.Control $result × $localsType:ident)
    (.arg Complexity.Language.Heap .pure))
  let type ← quantifyScope site.scope (← `(∀ ($post:ident : $postType),
    Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
      (ps := .arg Complexity.Language.Heap .pure) $invocation
      (fun $heap:ident =>
        ((Std.Do.WP.wp $bodyInvocation).apply
          (fun $outcome:ident $finish:ident => ⟨
            Complexity.Language.ScopeSafe $heap:ident
              ⟨($view:ident).symm ($outcome:ident).2, $finish:ident⟩ ($outcome:ident).1 ∧
            (($post:ident).1 $outcome:ident
              (Complexity.Language.Heap.take $finish:ident ($heap:ident).objects.size)).down⟩,
            ⟨⟩)) $heap:ident) $post:ident))
  let proof ← curryScope site.scope (← `(fun $post:ident =>
    Complexity.Language.Stmt.observe_scope_safe_spec $view:ident $program:ident
      $body:ident $tuple $post:ident))
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Compose the actual body specification with safe scratch release. Surviving
    locals and return values stay rooted; current retained contents are not rolled back. -/
    theorem $name:ident : $type := $proof)).raw

private def observationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let mut arguments ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let type ← typeTerm param.type
    let parameter := param.name
    arguments ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $arguments)
  let result ← valueTypeTerm fn.result
  let mut type ← `(ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result)
  let mut value ← `(Complexity.Language.Program.eval $programName:ident $id:ident $arguments)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    value ← `(fun ($parameter:ident : $parameterType) => $value)
  let declaration ← `(command|
    /-- The named function's actual partial source action, with ordinary typed arguments
    and an explicitly supplied shared heap. -/
    noncomputable def $name:ident : $type := $value)
  return declaration.raw

private def calleeObservationDeclaration (family program : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name "_observe"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let env ← freshProofName fn.name `arguments
  let mut remaining ← `($env:ident)
  let mut values := #[]
  for _ in fn.params do
    values := values.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let applied := Lean.Syntax.mkApp ⟨observation.raw⟩ values
  let type ← `(∀ ($env:ident : Complexity.Language.Env $params),
    Complexity.Language.Program.eval $program:ident $id:ident $env:ident = $applied)
  let mut proof ← `((Complexity.Language.Env.forall_nil _).mpr (by rfl))
  for (param, index) in fn.params.zipIdx.reverse do
    let sourceType ← typeTerm param.type
    let valueType ← valueTypeTerm param.type
    let rest ← parameterTypes (fn.params.extract (index + 1) fn.params.size)
    proof ← `((Complexity.Language.Env.forall_cons (τ := $sourceType) (Γ := $rest) _).mpr
      (fun ($(param.name):ident : $valueType) => $proof))
  return (← `(command|
    /-- Fold an actual source invocation back to its named ordinary-argument observation. -/
    theorem $name:ident : $type := $proof)).raw

private def equationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (lowered : LoweredBlock)
    (importFolds : Array (TSyntax `ident)) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name (if pureMode then "_action_eq" else "_eq")
  let observation := actionName family fn.name pureMode
  let bodyName := generatedName family fn.name "Body"
  let id := generatedName family fn.name "Id"
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let lhs := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let fallthrough ← `(doElem| throw Complexity.Language.Fault.missingReturn)
  let body := lowered.proofSequence fallthrough
  let result ← valueTypeTerm fn.result
  let loopContinuations ← namedSimpArgs (lowered.sites.map fun site => loopMember site "continue_eq")
  let loopViews ← namedSimpArgs (lowered.sites.flatMap fun site =>
    #[loopMember site "view_apply", loopMember site "view_symm_apply"])
  let compositionArgs ← constantSimpArgs #[``Complexity.Language.Stmt.evalWith_skip,
    ``Complexity.Language.Stmt.evalWith_ret, ``Complexity.Language.Stmt.evalWith_assign,
    ``Complexity.Language.Stmt.evalWith_letPrim, ``Complexity.Language.Stmt.evalWith_seq,
    ``Complexity.Language.Stmt.evalWith_ite, ``Complexity.Language.Stmt.evalWith_matchOption,
    ``Complexity.Language.Stmt.evalWith_call,
    ``Complexity.Language.Stmt.evalWith_read, ``Complexity.Language.Stmt.evalWith_write,
    ``Complexity.Language.Stmt.evalWith_slice, ``Complexity.Language.Stmt.evalWith_alloc]
  let allArgs := (← namedSimpArgs (#[bodyName] ++ importFolds)) ++ loopContinuations ++ loopViews ++
    (← viewSimpArgs) ++ compositionArgs ++ (← valueSimpArgs) ++
    (← constantSimpArgs #[``Complexity.Language.Env.tail_set_here,
      ``Complexity.Language.Env.tail_set_there, ``ExceptT.bind_throw])
  let mut type ← `($lhs = ((do $body:doSeq) : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof ← `(by
    have body_selected : ($programName:ident).body $id:ident = $bodyName:ident := rfl
    conv =>
      lhs
      unfold $observation:ident
      rw [Complexity.Language.Program.eval_eq_evalWith, body_selected]
    simp only [$allArgs,*]
    -- The semantic and native Option eliminators can have different motives.
    -- Compare actual bind results and branches without unfolding any callee.
    all_goals repeat' first
      | rfl
      | (split <;> simp_all only [Option.some.injEq, reduceCtorEq])
      | (congr 1; funext value)
    all_goals rfl)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  let declaration ← `(command|
    /-- One source-body equation in ordinary monadic notation; named callees remain opaque. -/
    theorem $name:ident : $type := $proof)
  return declaration.raw

private def argumentsDeclaration (family : TSyntax `ident) (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_args"
  let params ← parameterTypes fn.params
  let mut type ← `(Complexity.Language.Env $params)
  let mut value ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let sourceType ← typeTerm param.type
    value ← `(Complexity.Language.Env.cons (τ := $sourceType) $parameter:ident $value)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    value ← `(fun ($parameter:ident : $parameterType) => $value)
  return (← `(command|
    /-- The actual declared argument environment, constructed from ordinary source parameters.
    This is proof-side parameter transport, not an additional runtime operation. -/
    abbrev $name:ident : $type := $value)).raw

private def totalDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM (Array Syntax) := do
  let name := generatedName family fn.name "_total_iff"
  let contractName := generatedName family fn.name "_contract"
  let onArgsName := generatedName family fn.name "_onArgs"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let pre := mkIdent (← Macro.addMacroScope `pre)
  let post := mkIdent (← Macro.addMacroScope `post)
  let env := mkIdent (← Macro.addMacroScope `env)
  let initialHeap := mkIdent (← Macro.addMacroScope `initialHeap)
  let value := mkIdent (← Macro.addMacroScope `value)
  let finalHeap := mkIdent (← Macro.addMacroScope `finalHeap)
  let result ← valueTypeTerm fn.result
  let mut preType ← `(Complexity.Language.Heap → Prop)
  let mut postType ← `(Complexity.Language.Heap → $result → Complexity.Language.Heap → Prop)
  for param in fn.params.reverse do
    let type ← valueTypeTerm param.type
    preType ← `($type → $preType)
    postType ← `($type → $postType)
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let mut envArguments : Array (TSyntax `term) := #[]
  let mut remaining ← `($env:ident)
  for _ in fn.params do
    envArguments := envArguments.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let codomain := mkIdent (← Macro.addMacroScope `α)
  let function := mkIdent (← Macro.addMacroScope `function)
  let mut functionType : TSyntax `term := ⟨codomain.raw⟩
  for param in fn.params.reverse do
    let type ← valueTypeTerm param.type
    functionType ← `($type → $functionType)
  let applied := Lean.Syntax.mkApp ⟨function.raw⟩ envArguments
  let params ← parameterTypes fn.params
  let onArgsDeclaration ← `(command|
    /-- Apply a predicate, postcondition or bound with ordinary source parameters
    to the actual argument environment. No new contract or execution is introduced. -/
    abbrev $onArgsName:ident {$codomain:ident : Sort _}
        ($function:ident : $functionType) ($env:ident : Complexity.Language.Env $params) :
        $codomain:ident := $applied)
  let ordinaryPre := Lean.Syntax.mkApp ⟨pre.raw⟩ (arguments.push ⟨initialHeap.raw⟩)
  let ordinaryPost := Lean.Syntax.mkApp ⟨post.raw⟩
    (arguments ++ #[⟨initialHeap.raw⟩, ⟨value.raw⟩, ⟨finalHeap.raw⟩])
  let invocation := Lean.Syntax.mkApp ⟨observation.raw⟩ (arguments.push ⟨initialHeap.raw⟩)
  let mut ordinary ← `(∀ ($initialHeap:ident : Complexity.Language.Heap),
    $ordinaryPre → ∃ ($value:ident : $result) ($finalHeap:ident : Complexity.Language.Heap),
      $invocation = Part.some (.ok $value:ident, $finalHeap:ident) ∧ $ordinaryPost)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    ordinary ← `(∀ ($parameter:ident : $type), $ordinary)
  let hypothesis := mkIdent (← Macro.addMacroScope `specification)
  let mut encodedArgs ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← typeTerm param.type
    encodedArgs ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $encodedArgs)
  let mut forward ← `($hypothesis:ident $encodedArgs)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    forward ← `(fun ($parameter:ident : $type) => $forward)
  forward ← `(fun $hypothesis:ident => $forward)
  let mut backward := Lean.Syntax.mkApp ⟨hypothesis.raw⟩ arguments
  backward ← `((Complexity.Language.Env.forall_nil _).mpr $backward)
  for (param, index) in fn.params.zipIdx.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    let sourceType ← typeTerm param.type
    let remainingTypes ← parameterTypes (fn.params.extract (index + 1) fn.params.size)
    backward ← `((Complexity.Language.Env.forall_cons (τ := $sourceType)
      (Γ := $remainingTypes) _).mpr (fun ($parameter:ident : $type) => $backward))
  backward ← `(fun $hypothesis:ident => $backward)
  let contractDeclaration ← `(command|
    /-- Budget-free total correctness with ordinary source parameters and relational
    initial/final heap postconditions. This is the existing source function contract. -/
    abbrev $contractName:ident ($pre:ident : $preType) ($post:ident : $postType) : Prop :=
      Complexity.Language.FunctionTotal $programName:ident $id:ident
        ($onArgsName:ident $pre:ident) ($onArgsName:ident $post:ident))
  let declaration ← `(command|
    /-- The source contract is equivalent to ordinary curried preconditions and
    successful result/heap postconditions, including termination and absence of faults. -/
    theorem $name:ident ($pre:ident : $preType) ($post:ident : $postType) :
        $contractName:ident $pre:ident $post:ident ↔ $ordinary := by
      rw [$contractName:ident, Complexity.Language.FunctionTotal.iff_eval]
      exact ⟨$forward, $backward⟩)
  return #[onArgsDeclaration.raw, contractDeclaration.raw, declaration.raw]

private def specificationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name "_spec"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let result ← valueTypeTerm fn.result
  let pre := mkIdent (← Macro.addMacroScope `pre)
  let post := mkIdent (← Macro.addMacroScope `post)
  let contract := mkIdent (← Macro.addMacroScope `contract)
  let continuation := mkIdent (← Macro.addMacroScope `continuation)
  let initialHeap := mkIdent (← Macro.addMacroScope `initialHeap)
  let value := mkIdent (← Macro.addMacroScope `value)
  let finalHeap := mkIdent (← Macro.addMacroScope `finalHeap)
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let invocation := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let mut encodedArgs ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← typeTerm param.type
    encodedArgs ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $encodedArgs)
  let mut type ← `(∀ ($continuation:ident : Std.Do.PostCond $result
      (.except Complexity.Language.Fault (.arg Complexity.Language.Heap .pure))),
    Std.Do.Triple (m := ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part))
      (ps := .except Complexity.Language.Fault (.arg Complexity.Language.Heap .pure))
      $invocation
      (fun $initialHeap:ident => ⟨$pre:ident $encodedArgs $initialHeap:ident ∧
        ∀ $value:ident $finalHeap:ident,
          $post:ident $encodedArgs $initialHeap:ident $value:ident $finalHeap:ident →
            (($continuation:ident).1 $value:ident $finalHeap:ident).down⟩)
      $continuation:ident)
  let mut proof ← `(fun $continuation:ident =>
    Complexity.Language.FunctionTotal.triple_spec $contract:ident $encodedArgs $continuation:ident)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Apply a supplied source contract with ordinary named arguments and its
    actual returned value and final heap. No callee body or new contract is inferred. -/
    theorem $name:ident
        {$pre:ident : Complexity.Language.Env $params → Complexity.Language.Heap → Prop}
        {$post:ident : Complexity.Language.Env $params → Complexity.Language.Heap →
          $result → Complexity.Language.Heap → Prop}
        ($contract:ident : Complexity.Language.FunctionTotal $programName:ident $id:ident
          $pre:ident $post:ident) : $type := $proof)).raw

private def importedDeclarations (family : TSyntax `ident)
    (imports : Array ImportedProgram) : MacroM (Option ImportDeclarations) := do
  let some first := imports[0]? | return none
  let mut program : TSyntax `term := ⟨(mkCIdent (first.family ++ `program)).raw⟩
  let mut signatures : TSyntax `term := ⟨(mkCIdent (first.family ++ `signatures)).raw⟩
  let mut embeddings : Array ImportEmbedding := #[⟨first,
    ← `(Complexity.Language.SignatureMap.refl $signatures),
    ← `(Complexity.Language.Program.Embeds.refl $program)⟩]
  for imported in imports.toList.drop 1 do
    let next : TSyntax `term := ⟨(mkCIdent (imported.family ++ `program)).raw⟩
    let nextSignatures : TSyntax `term := ⟨(mkCIdent (imported.family ++ `signatures)).raw⟩
    let leftMap ← `(Complexity.Language.SignatureMap.appendLeft $signatures $nextSignatures)
    let leftProof ← `(Complexity.Language.Program.embeds_link_left $program $next)
    embeddings ← embeddings.mapM fun entry => do
      return { entry with
        map := ← `(Complexity.Language.SignatureMap.trans $(entry.map) $leftMap)
        proof := ← `(Complexity.Language.Program.Embeds.trans $(entry.proof) $leftProof) }
    embeddings := embeddings.push ⟨imported,
      ← `(Complexity.Language.SignatureMap.appendRight $signatures $nextSignatures),
      ← `(Complexity.Language.Program.embeds_link_right $program $next)⟩
    program ← `(Complexity.Language.Program.link $program $next)
    signatures ← `($signatures ++ $nextSignatures)
  let signaturesName := mkIdentFrom family (family.getId ++ `importedSignatures)
  let programName := mkIdentFrom family (family.getId ++ `importedProgram)
  let signatureDeclaration ← `(command|
    /-- The complete signature tables retained from imported source programs. -/
    abbrev $signaturesName:ident : List Complexity.Language.Signature := $signatures)
  let programDeclaration ← `(command|
    /-- Actual imported function bodies with their internal calls relocated. -/
    def $programName:ident : Complexity.Language.Program $signaturesName:ident := $program)
  return some ⟨#[signatureDeclaration.raw, programDeclaration.raw],
    ⟨programName.raw⟩, ⟨signaturesName.raw⟩, embeddings⟩

private def importedObservationDeclaration (program map embedded : TSyntax `ident)
    (source : ImportedProgram) (fn : FunctionInfo) (callee : Callee) : MacroM Syntax := do
  let params ← parameterTypes callee.params
  let env ← freshProofName callee.name `arguments
  let originalId := mkCIdent (source.family ++ Name.mkSimple (fn.name.toString ++ "Id"))
  let originalFold := mkCIdent (source.family ++ Name.mkSimple (fn.name.toString ++ "_observe"))
  let mut remaining ← `($env:ident)
  let mut arguments := #[]
  for _ in callee.params do
    arguments := arguments.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let observed := Lean.Syntax.mkApp ⟨callee.observation.raw⟩ arguments
  return (← `(command|
    /-- Reuse an imported native action through the proved embedding of its real body. -/
    theorem $(callee.fold):ident ($env:ident : Complexity.Language.Env $params) :
        Complexity.Language.Program.eval $program:ident $(callee.id):ident $env:ident =
          $observed := by
      change Complexity.Language.SignatureMap.eval $map:ident $program:ident
        $originalId:ident $env:ident = _
      rw [Complexity.Language.Program.Embeds.eval_eq $embedded:ident]
      exact $originalFold:ident $env:ident)).raw

private def pureValueType : Ty → Bool
  | .nat | .bool | .unit => true
  | .buffer _ => false
  | .prod left right => pureValueType left && pureValueType right
  | .option value => pureValueType value

-- These identifiers were resolved by the source parser, and local proof
-- variables have fresh names. Replacing them cannot capture a source binder.
private def pureBody (callees : Array Callee) (body : LoweredBlock) :
    MacroM (TSyntax ``doSeq) := do
  let mut elements := #[]
  for element in body.proofBody do
    let replaced ← element.raw.replaceM fun node => do
      if node.isIdent then
        if let some callee := callees.find? (fun fn => fn.observation.getId == node.getId) then
          let some native := callee.native
            | Macro.throwErrorAt node
                "a pure source function can only call another proved pure source function"
          return some native.raw
      return none
    elements := elements.push (⟨replaced⟩ : TSyntax `doElem)
  return ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩

-- Native Lean checks each self-recursive definition. Acyclic inter-function
-- calls are emitted in dependency order, including forward source references.
private def pureFunctionOrder (family : TSyntax `ident) (functions : Array Function)
    (bodies : Array LoweredBlock) : MacroM (Array (Function × LoweredBlock)) := do
  let mut pending := (functions.zip bodies).toList
  let mut ordered : Array (Function × LoweredBlock) := #[]
  while !pending.isEmpty do
    let some next := pending.find? (fun (fn, body) =>
        pending.all fun (dependency, _) => dependency.name.getId == fn.name.getId ||
          !body.proofBody.any
            (fun element => element.raw.hasIdent
              (actionName family dependency.name true).getId))
      | Macro.throwErrorAt family
          "the pure frontend currently supports self recursion and acyclic named calls, not mutually recursive families"
    ordered := ordered.push next
    pending := pending.filter (fun entry => entry.1.name.getId != next.1.name.getId)
  return ordered

private def nativeDeclaration (family : TSyntax `ident) (fn : Function)
    (callees : Array Callee) (body : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name ""
  let parameters ← fn.params.mapM fun param => do
    let parameterType ← valueTypeTerm param.type
    `(bracketedBinder| ($(param.name):ident : $parameterType))
  let result ← valueTypeTerm fn.result
  let nativeBody ← pureBody callees body
  return (← `(command|
    /-- Executable total value function generated from the same buffer-free source block. -/
    def $name:ident $parameters:bracketedBinder* : $result :=
      Id.run (do $nativeBody:doSeq)
      $(fn.termination):suffix)).raw

private def pureCorrespondenceDeclaration (family : TSyntax `ident) (fn : Function)
    (callees : Array Callee) (body : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name "_action_eq_pure"
  let action := actionName family fn.name true
  let equation := generatedName family fn.name "_action_eq"
  let native := generatedName family fn.name ""
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let actual := Lean.Syntax.mkApp ⟨action.raw⟩ arguments
  let value := Lean.Syntax.mkApp ⟨native.raw⟩ arguments
  let result ← valueTypeTerm fn.result
  let dependencies := callees.filter fun callee =>
    callee.observation.getId != action.getId &&
      body.proofBody.any (fun element => element.raw.hasIdent callee.observation.getId)
  let equations := dependencies.map fun callee =>
    mkIdentFrom callee.observation
      (callee.observation.getId.getPrefix ++
        Name.mkSimple (callee.observation.getId.getString! ++ "_eq_pure"))
  let mut type ← `($actual = (pure $value : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof ← `(by
    source_pure_correspondence $value using $equation:ident [$equations:ident,*])
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    /-- The actual source action terminates with the generated native result and
    preserves every initial heap. Lean's native recursion principle proves this once. -/
    theorem $name:ident : $type := $proof)).raw

private def pureTotalDeclaration (family program : TSyntax `ident)
    (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_total"
  let native := generatedName family fn.name ""
  let observed := generatedName family fn.name "_observe"
  let correspondence := generatedName family fn.name "_action_eq_pure"
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let env ← freshProofName fn.name `arguments
  let initial ← freshProofName fn.name `initialHeap
  let finalHeap ← freshProofName fn.name `finalHeap
  let returned ← freshProofName fn.name `value
  let mut remaining ← `($env:ident)
  let mut values := #[]
  for _ in fn.params do
    values := values.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let value := Lean.Syntax.mkApp ⟨native.raw⟩ values
  return (← `(command|
    /-- Exact total source contract inherited from the generated native function. -/
    theorem $name:ident :
        Complexity.Language.FunctionTotal $program:ident $id:ident (fun _ _ => True)
          (fun $env:ident $initial:ident $returned:ident $finalHeap:ident =>
            $returned:ident = $value ∧ $finalHeap:ident = $initial:ident) := by
      apply Complexity.Language.FunctionTotal.of_eval_eq_pure
        (program := $program:ident) (fn := $id:ident)
        (fun ($env:ident : Complexity.Language.Env $params) => $value)
      · intro $env:ident
        rw [$observed:ident, $correspondence:ident]
      · intro _ _ _
        exact ⟨rfl, rfl⟩)).raw

private def programDeclarations (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) (imports : Array ImportedProgram)
    (pureMode : Bool) :
    MacroM (Syntax × Array FunctionInfo) := do
  let mut functions : Array Function := #[]
  for source in sources do
    let fn ← parseFunction source
    if functions.any (fun previous => previous.name.getId == fn.name.getId) then
      Macro.throwErrorAt fn.name "duplicate source function name"
    if pureMode then
      unless pureValueType fn.result && fn.params.all (pureValueType ·.type) do
        Macro.throwErrorAt fn.name
          "pure source functions support Nat, Bool, Unit and their products/options, but no nested buffers"
    functions := functions.push fn
  let signaturesName := mkIdentFrom family (family.getId ++ `signatures)
  let localSignaturesName := mkIdentFrom family (family.getId ++ `localSignatures)
  let localBodiesName := mkIdentFrom family (family.getId ++ `localBodies)
  let programName := mkIdentFrom family (family.getId ++ `program)
  let signatures ← functions.mapM fun fn => do
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    `(({ params := $params, result := $result } : Complexity.Language.Signature))
  let imported ← importedDeclarations family imports
  let mut declarations := imported.map (·.declarations) |>.getD #[]
  let signatureValue ← match imported with
    | none => `([$signatures,*])
    | some imported => do
        declarations := declarations.push (← `(command|
          /-- Signatures of the functions added by this source declaration. -/
          abbrev $localSignaturesName:ident : List Complexity.Language.Signature :=
            [$signatures,*])).raw
        `($localSignaturesName:ident ++ $(imported.signatures))
  let signatureDeclaration ← `(command|
    /-- The source program's declared first-order signatures. -/
    abbrev $signaturesName:ident : List Complexity.Language.Signature := $signatureValue)
  declarations := declarations.push signatureDeclaration.raw
  for (fn, index) in functions.zipIdx do
    let id := generatedName family fn.name "Id"
    let number := Syntax.mkNumLit (toString index)
    let declaration ← `(command|
      /-- This named source function's index in its declared signature table. -/
      abbrev $id:ident : Fin ($signaturesName:ident).length := ⟨$number:num, by decide⟩)
    declarations := declarations.push declaration.raw
  let mut callees : Array Callee := functions.map fun fn =>
    ⟨fn.name, fn.params, fn.result, generatedName family fn.name "Id",
      actionName family fn.name pureMode, generatedName family fn.name "_observe",
      if pureMode then some (generatedName family fn.name "") else none⟩
  let mut importedProofs : Array Syntax := #[]
  let mut importedObservations : Array Syntax := #[]
  let mut importFolds : Array (TSyntax `ident) := #[]
  if let some imported := imported then
    for entry in imported.embeddings do
      let importNamespace := family.getId ++ `imports ++ entry.source.name.getId
      let map := mkIdentFrom entry.source.name (importNamespace ++ `map)
      let embedded := mkIdentFrom entry.source.name (importNamespace ++ `embedding)
      let sourceSignatures := mkCIdent (entry.source.family ++ `signatures)
      let sourceProgram := mkCIdent (entry.source.family ++ `program)
      declarations := declarations.push (← `(command|
        /-- Signature-preserving positions of this imported source program. -/
        abbrev $map:ident : Complexity.Language.SignatureMap
            $sourceSignatures:ident $signaturesName:ident :=
          Complexity.Language.SignatureMap.trans $(entry.map)
            (Complexity.Language.SignatureMap.appendRight
              $localSignaturesName:ident $(imported.signatures)))).raw
      importedProofs := importedProofs.push (← `(command|
        /-- The imported functions retain their actual relocated bodies. -/
        theorem $embedded:ident : Complexity.Language.Program.Embeds
            $sourceProgram:ident $map:ident $programName:ident :=
          Complexity.Language.Program.Embeds.trans $(entry.proof)
            (Complexity.Language.Program.embeds_extend $(imported.program)
              $localSignaturesName:ident $localBodiesName:ident))).raw
      for fn in entry.source.functions do
        let name := mkIdentFrom entry.source.name (entry.source.name.getId ++ fn.name)
        if callees.any (fun previous => previous.name.getId == name.getId) then
          Macro.throwErrorAt name "ambiguous source function name"
        let id ← freshProofName family `sourceImportedFunction
        let fold ← freshProofName family `sourceImportedObservation
        let originalId := mkCIdent (entry.source.family ++ Name.mkSimple (fn.name.toString ++ "Id"))
        declarations := declarations.push (← `(command|
          /-- The actual target index of an imported function. -/
          abbrev $id:ident : Fin ($signaturesName:ident).length :=
            Complexity.Language.SignatureMap.toFun $map:ident $originalId:ident)).raw
        let callee : Callee := ⟨name,
          fn.params.map (fun param => ⟨mkIdentFrom entry.source.name param.1, param.2⟩),
          fn.result, id,
          mkCIdent (entry.source.family ++
            Name.mkSimple (fn.name.toString ++ if fn.pure then "_action" else "")), fold,
          if fn.pure then some (mkCIdent (entry.source.family ++ fn.name)) else none⟩
        callees := callees.push callee
        importFolds := importFolds.push fold
        importedObservations := importedObservations.push (← importedObservationDeclaration
          programName map embedded entry.source fn callee)
  let mut loweredBodies : Array LoweredBlock := #[]
  for fn in functions do
    let name := generatedName family fn.name "Body"
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    let body ← functionCode family callees fn
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.alloc then
      Macro.throwErrorAt fn.name
        "buffer allocation is effectful and is not supported by 'source_program (pure)'"
    if pureMode then
      if body.sites.any (fun site => site.guard.isNone) then
        Macro.throwErrorAt fn.name
          "scratch allocation scopes are effectful and are not supported by 'source_program (pure)'"
      unless body.sites.isEmpty do
        Macro.throwErrorAt fn.name
          "the pure frontend currently supports recursive calls, not while loops"
      if body.fallsThrough then
        Macro.throwErrorAt fn.name "every pure source function path must return a value"
    loweredBodies := loweredBodies.push body
    for site in body.sites do
      declarations := declarations ++ (← loopCodeDeclarations signaturesName site)
    let declaration ← `(command|
      /-- The named function's actual independently interpreted source body. -/
      def $name:ident : Complexity.Language.Stmt $signaturesName:ident $params $result := $(body.term))
    declarations := declarations.push declaration.raw
  let mut bodies ← `(fun index => Fin.elim0 index)
  for fn in functions.reverse do
    let name := generatedName family fn.name "Body"
    bodies ← `(Fin.cases $name:ident $bodies)
  let programValue ← match imported with
    | none => `(({ body := $bodies } : Complexity.Language.Program $signaturesName:ident))
    | some imported => do
        declarations := declarations.push (← `(command|
          /-- Added function bodies already typed against the complete linked table. -/
          def $localBodiesName:ident : (fn : Fin ($localSignaturesName:ident).length) →
              Complexity.Language.Stmt $signaturesName:ident
                ($localSignaturesName:ident)[fn].params ($localSignaturesName:ident)[fn].result :=
            $bodies)).raw
        `(Complexity.Language.Program.extend $(imported.program)
          $localSignaturesName:ident $localBodiesName:ident)
  let programDeclaration ← `(command|
    /-- The finite table of actual named source bodies. -/
    def $programName:ident : Complexity.Language.Program $signaturesName:ident := $programValue)
  declarations := declarations.push programDeclaration.raw
  declarations := declarations ++ importedProofs ++ importedObservations
  for fn in functions do
    declarations := declarations.push (← argumentsDeclaration family fn)
  for fn in functions do
    declarations := declarations.push (← observationDeclaration family programName fn pureMode)
  for fn in functions do
    declarations := declarations.push (← calleeObservationDeclaration family programName fn pureMode)
  let calleeFolds := callees.map (·.fold)
  let loopSites := loweredBodies.flatMap (·.sites)
  for site in loopSites do
    declarations := declarations ++ (← loopObservationDeclarations programName site)
    if site.guard.isSome then
      declarations := declarations ++ (← loopCaptureDeclarations site)
  for site in loopSites do
    declarations := declarations ++ (← loopEquationDeclarations site loopSites calleeFolds)
    declarations := declarations.push (← loopContinuationDeclaration programName site loopSites)
    if site.guard.isSome then
      declarations := declarations ++ (← loopCaptureFrameDeclarations programName site loopSites)
      declarations := declarations.push (← loopTerminationDeclaration programName site false)
      declarations := declarations.push (← loopTerminationDeclaration programName site true)
    else
      declarations := declarations.push (← scopeSpecificationDeclaration programName site)
  for fn in functions, body in loweredBodies do
    declarations := declarations.push
      (← equationDeclaration family programName fn body importFolds pureMode)
  for fn in functions do
    declarations := declarations ++ (← totalDeclaration family programName fn pureMode)
    declarations := declarations.push (← specificationDeclaration family programName fn pureMode)
  if pureMode then
    let order ← pureFunctionOrder family functions loweredBodies
    for (fn, body) in order do
      declarations := declarations.push
        (← nativeDeclaration family fn callees body)
      declarations := declarations.push
        (← pureCorrespondenceDeclaration family fn callees body)
      declarations := declarations.push
        (← pureTotalDeclaration family programName fn)
  return (mkNullNode declarations, functions.map fun fn =>
    ⟨fn.name.getId, fn.params.map (fun param => (param.name.getId, param.type)), fn.result, pureMode⟩)

private def elaborateProgram (family : TSyntax `ident)
    (functions : Array (TSyntax `sourceFunction)) (libraries : Array (TSyntax `ident))
    (pureMode : Bool := false) :
    Lean.Elab.Command.CommandElabM Unit := do
  for source in functions do
    let fn ← Lean.Elab.liftMacroM (parseFunction source)
    let hints ← Lean.Elab.elabTerminationHints fn.termination
    if pureMode then
      if hints.partialFixpoint?.isSome then
        Lean.throwErrorAt fn.termination "pure source functions must terminate; partial fixed points are not supported"
    else if hints.isNotNone then
      Lean.throwErrorAt fn.termination "termination hints are checked by 'source_program (pure)'"
  let mut imports : Array ImportedProgram := #[]
  for library in libraries do
    let (name, functions) ← getProgramInfo library
    if imports.any (fun imported => imported.family == name) then
      Lean.throwErrorAt library "duplicate source program import"
    imports := imports.push ⟨library, name, functions⟩
  let (declarations, information) ←
    Lean.Elab.liftMacroM (programDeclarations family functions imports pureMode)
  Lean.Elab.Command.elabCommand declarations
  registerProgramInfo family information

elab_rules : command
  | `(command| source_program $family:ident where $functions:sourceFunction*) => do
      elaborateProgram family functions #[]
  | `(command| source_program $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => do
      elaborateProgram family functions libraries.getElems
  | `(command| source_program (pure) $family:ident where $functions:sourceFunction*) => do
      elaborateProgram family functions #[] true
  | `(command| source_program (pure) $family:ident importing $libraries:ident,* where
      $functions:sourceFunction*) => do
      elaborateProgram family functions libraries.getElems true

end Complexity.Language.Syntax
