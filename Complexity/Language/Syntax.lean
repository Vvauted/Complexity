/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Continuation
import Complexity.Language.Eval.Verification
import Complexity.Language.Eval.Node.Verification
import Complexity.Language.Eval.Locals.Composition
import Complexity.Language.Eval.Locals.Continuation
import Complexity.Language.Eval.Locals.Effects
import Complexity.Language.Eval.Locals.Verification
import Complexity.Language.Eval.Locals.Captures
import Complexity.Language.Eval.Locals.Range
import Complexity.Language.Linking.Eval
import Complexity.Language.Linking.Extension
import Complexity.Language.Syntax.Imports
import Complexity.Language.Syntax.Pure
import Complexity.Language.RepresentedFunction
import Std.Do.WP.SimpLemmas
import Lean.Elab.Command
import Lean.Elab.Do
import Lean.Elab.PreDefinition.TerminationHint
import Lean.Elab.Tactic.Conv.Basic
import Lean.Meta.Closure
import Lean.Parser.Do
import Lean.PrettyPrinter.Delaborator

/-!
# Named source programs with shared buffers and allocation

`source_program P where` declares an independent typed source program from
Lean-style function headers and `do` blocks. The supported types are
`Nat`, `Bool`, `Unit`, Nat/Bool buffers and node references, products and `Option`, with lexical `let` and
`let mut`, assignment, named first-order calls, `if`/`then` with optional `else`,
`while` and `return`.
Only the nearest mutable binding may be assigned; ordinary `let` bindings and
parameters are immutable. `x ← action` rebinds a mutable local to the actual
result of a supported named call, buffer or node read, slice or allocation. Natural arithmetic and
comparisons may be nested in bindings, assignments, return values, conditions
and call arguments. Their operands are normalized left to right into actual
lexical primitive bindings; no host computation replaces the generated operations.
Natural comparisons include `<`, `≤`/`<=`, `>` and `≥`/`>=`; `=`/`==` and
`≠`/`!=` compare either two naturals or two Booleans. Boolean `!`, `&&` and `||`
use actual typed branches. The right operand of `&&` or `||` is evaluated only
in its selected branch, including its normalized intermediate operations.

Products use ordinary pairs and `.1`/`.2` or `.fst`/`.snd` projections. Options
use `none`, `some value` and an exhaustive `match` with `none` and `some value`
branches. The payload exists only in the latter branch; leaving it preserves
the actual heap and outer mutable locals. Expected parameter, binding and
return types supply the type of `none`; otherwise give an ordinary type annotation.
Immutable bindings also accept nested product patterns and `_`, including
`let (x, y) ← call` and `some (x, y)` branches. The right-hand side is evaluated
once; named fields are obtained by actual primitive projections and copies.

Source functions support `for i in [:stop]`, `for i in [start:stop]` and
explicit positive strides `[start:stop:step]` or `[:stop:step]`. Bounds and the
stride are frozen; the index is immutable. A literal or immutable Nat local may
be reused directly, as may an immutable buffer's length in the guard. Other
expressions are captured once. The actual guard, increment and capture work
remain counted. Lean checks stride positivity using `omega`, including dynamic
expressions such as `k + 1`; zero or an unproved positive stride is rejected,
not silently changed into a different range.
`for x in xs` borrows a
fixed buffer view and reads its current cell on each iteration, not a snapshot.
These constructs lower to the existing while semantics and named-loop rules.
Pure finite ranges also generate executable native Lean iteration and its
source correspondence. `source_pure_simp [P.f]` reduces an always-continuing
native range to ordinary fold mathematics without return flags or cursor
bookkeeping. Pure unbounded `while`, `break` and `continue` are not supported.

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

`NodeRef Nat` and `NodeRef Bool` denote typed immutable-node handles in effectful
parameters, results, products and options. Passing or copying a handle preserves
its identity. `let (head, tail) ← ref.read` reads the actual stored payload and
optional shared tail using `Stmt.readNode`; its generated monadic equation uses
`NodeRef.readM`. The receiver must be a node handle, not an `Option`: match an
optional root before reading it. Reading also supports `let mut` and rebinding;
a missing or wrongly typed node faults without changing the current heap.
`let ref ← NodeRef.cons head tail` allocates one immutable node with a Nat or
Bool payload and a same-kind optional tail, returning its actual fresh handle.
The generated `Stmt.consNode` and `NodeRef.consM` equation neither scan nor
validate the shared tail. Construction also supports `let mut` and rebinding.
These operations do not provide a native List facade. Node reads, construction
and node-reference parameters and results are excluded from the heap-free pure
frontend, including handles nested inside products or options. Finite-machine
capacity and word ranges remain separate compilation obligations.

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

/-- Checked coordinate rewrite declarations belonging to one generated source loop.
The key is its actual `Code` declaration; no body, semantics or cost is stored here. -/
structure LoopCoordinates where
  rules : Array Name

private initialize loopCoordinatesExt :
    SimplePersistentEnvExtension (Name × LoopCoordinates) (NameMap LoopCoordinates) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
  }

/-- Find the coordinate rules registered for an actual generated loop body. -/
def getLoopCoordinates? (env : Environment) (code : Name) : Option LoopCoordinates :=
  (loopCoordinatesExt.getState env).find? code

private structure LoopCoordinateRegistration where
  code : TSyntax `ident
  rules : Array (TSyntax `ident)
  nativeTypes : Array (TSyntax `term)

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

-- Preserve finite-range origin until both source and native views are emitted.
syntax (name := sourceFiniteRange)
  "source_range% " "(" ident "," term "," term ")" " do " doSeq : doElem

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

private structure Parameter where
  name : TSyntax `ident
  type : Ty

private structure NativeView where
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

private structure Function where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  body : TSyntax `term
  termination : TSyntax ``Lean.Parser.Termination.suffix
  nativeView : Option NativeView := none

private structure Callee where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  id : TSyntax `ident
  observation : TSyntax `ident
  fold : TSyntax `ident
  native : Option (TSyntax `ident) := none
  pureEquation : Option (TSyntax `ident) := none

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

private structure NativeCoordinate where
  type : TSyntax `term
  equiv : TSyntax `term

private structure Binding where
  name : Option Name
  proofName : TSyntax `ident
  type : Ty
  isMutable : Bool
  native : Option NativeCoordinate := none

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

private structure FiniteRange where
  cursor : TSyntax `ident
  stop : TSyntax `term
  stride : TSyntax `term
  body : Array (TSyntax `doElem)
  fallsThrough : Bool

private structure BlockSite where
  name : TSyntax `ident
  scope : Scope
  result : Ty
  guard : Option (TSyntax `term)
  body : TSyntax `term
  finiteRange : Option FiniteRange
  nativeResult : Option NativeCoordinate := none

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
  | .node .nat => "NodeRef Nat"
  | .node .bool => "NodeRef Bool"
  | .prod left right => s!"({typeName left} × {typeName right})"
  | .option value => s!"Option ({typeName value})"

private partial def parseType (stx : TSyntax `term) : MacroM Ty := do
  match stx with
  | `(source_native_type% ($raw) ($_native) via ($_equiv)) => parseType raw
  | `(source_native_type% ($raw) ($_native)) => parseType raw
  | `(($type:term)) => parseType type
  | `(Nat) => return .nat
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | `(Buffer Nat) => return .buffer .nat
  | `(Buffer Bool) => return .buffer .bool
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.nat) => return .buffer .nat
  | `(Complexity.Language.Buffer Complexity.Language.CellTy.bool) => return .buffer .bool
  | `(NodeRef Nat) => return .node .nat
  | `(NodeRef Bool) => return .node .bool
  | `(Complexity.Language.NodeRef Complexity.Language.CellTy.nat) => return .node .nat
  | `(Complexity.Language.NodeRef Complexity.Language.CellTy.bool) => return .node .bool
  | `($left × $right) | `(Prod $left $right) =>
      return .prod (← parseType left) (← parseType right)
  | `(Option $value) => return .option (← parseType value)
  | _ =>
      Macro.throwErrorAt stx
        "supported source types are Nat, Bool, Unit, Buffer Nat/Bool, NodeRef Nat/Bool, products and Option"

private def typeTerm : Ty → MacroM (TSyntax `term)
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

private def valueTypeTerm : Ty → MacroM (TSyntax `term)
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

private def bindingNativeType (binding : Binding) : MacroM (TSyntax `term) :=
  match binding.native with
  | some native => pure native.type
  | none => valueTypeTerm binding.type

private def scopeNativeTypes (scope : Scope) : MacroM (TSyntax `term) := do
  let mut values ← `(Unit)
  for binding in scope.reverse do
    values ← `($(← bindingNativeType binding) × $values)
  return values

private def scopeNativeEquiv (scope : Scope) : MacroM (TSyntax `term) := do
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

private def decodeNativeField (binding : Binding) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  match binding.native with
  | some native => `(($(native.equiv)).symm $value)
  | none => pure value

private def encodeNativeFields (scope : Scope) (values : Array (TSyntax `term)) :
    MacroM (Array (TSyntax `term)) :=
  (scope.toArray.zip values).mapM fun (binding, value) => encodeNativeField binding value

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

private def curryNativeScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(fun ($(binding.proofName):ident : $(← bindingNativeType binding)) => $result)
  return result

private def quantifyNativeScope (scope : Scope) (body : TSyntax `term) : MacroM (TSyntax `term) := do
  let mut result := body
  for binding in scope.reverse do
    result ← `(∀ ($(binding.proofName):ident : $(← bindingNativeType binding)), $result)
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
      return ⟨name, params, ← parseType result, body, termination, none⟩
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
  | `(source_native% ($raw) ($_native) ($_nativeType) via ($_equiv)) => parseAtom scope raw
  | `(source_native% ($raw) ($_native) ($_nativeType)) => parseAtom scope raw
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

private def parseNodeRef (scope : Scope) (stx : TSyntax `term) : MacroM (CellTy × Atomic) := do
  let ref ← parseAtom scope stx
  match ref.type with
  | .node kind => return (kind, ref)
  | _ =>
      Macro.throwErrorAt stx
        s!"expected a source node reference, found {typeName ref.type}; match an optional root before reading it"

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

private def nativeProofValue (scope : Scope) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let value ← value.raw.replaceM fun node => do
    if node.isIdent then
      if let some binding := scope.find? (fun binding => binding.name == some node.getId) then
        return some binding.proofName.raw
    return none
  return ⟨value⟩

-- Hidden layout temporaries remain complete lexical coordinates of the loop.
-- Their native-side values encode already checked native operands; no source
-- instruction, temporary or charge is removed by this proof-side reconstruction.
private partial def rawValueInNativeScope (scope : Scope) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let value ← value.raw.replaceM fun node => do
    match node with
    | `(source_native% ($_raw) ($native) ($_type) via ($equiv)) =>
        return some (← `(($equiv : _ ≃ _) $native)).raw
    | `(source_native% ($raw) ($_native) ($_type)) =>
        return some (← rawValueInNativeScope scope raw).raw
    | `(source_raw_value% ($_raw) ($native)) => return some native.raw
    | `(source_raw_value% ($raw)) => return some (← rawValueInNativeScope scope raw).raw
    | _ => pure ()
    if node.isIdent then
      if let some binding := scope.find? (fun binding => binding.proofName.getId == node.getId) then
        if let some native := binding.native then
          return some (← `(($(native.equiv) : _ ≃ _) $(binding.proofName):ident)).raw
    return none
  return ⟨value⟩

private partial def parsePrimitive (scope : Scope) (stx : TSyntax `term)
    (expected : Option Ty := none) : MacroM Primitive := do
  if let `(source_raw_value% ($raw)) := stx then
    let parsed ← parsePrimitive scope raw expected
    let native ← rawValueInNativeScope scope parsed.value
    return { parsed with value := ← `(source_raw_value% ($(parsed.value)) ($native)) }
  if let `(source_raw_value% ($raw) ($_native)) := stx then
    let parsed ← parsePrimitive scope raw expected
    let native ← rawValueInNativeScope scope parsed.value
    return { parsed with value := ← `(source_raw_value% ($(parsed.value)) ($native)) }
  if let `(source_native% ($raw) ($native) ($nativeType) via ($equiv)) := stx then
    let parsed ← parsePrimitive scope raw expected
    let native ← nativeProofValue scope native
    return { parsed with value := ←
      `(source_native% ($(parsed.value)) ($native) ($nativeType) via ($equiv)) }
  if let `(source_native% ($raw) ($native) ($nativeType)) := stx then
    let parsed ← parsePrimitive scope raw expected
    let native ← nativeProofValue scope native
    return { parsed with value := ← `(source_native% ($(parsed.value)) ($native) ($nativeType)) }
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
  | `($left > $right) => binaryPrimitive scope right left .bool ``Prim.lt ``LT.lt
  | `($left ≥ $right) => binaryPrimitive scope right left .bool ``Prim.le ``LE.le
  | `($left >= $right) => binaryPrimitive scope right left .bool ``Prim.le ``LE.le
  | _ =>
      let atom ← parseAtom scope stx
      return ⟨atom.type, ← `(Complexity.Language.Prim.atom $(atom.term)), some atom.term,
        atom.value⟩

private def checkAnnotation (annotation : Option (TSyntax `term)) (actual : Ty) : MacroM Unit := do
  if let some annotation := annotation then
    expectType annotation actual (← parseType annotation)

private def bindingValueType (type : Ty) (annotation : Option (TSyntax `term))
    (value : Option (TSyntax `term) := none) :
    MacroM (TSyntax `term) := do
  if let some value := value then
    if let `(source_native% ($_raw) ($_native) ($nativeType) via ($equiv)) := value then
      return ← `(source_native_type% ($(← valueTypeTerm type)) ($nativeType) via ($equiv))
    if let `(source_native% ($_raw) ($_native) ($nativeType)) := value then
      return ← `(source_native_type% ($(← valueTypeTerm type)) ($nativeType))
  if let some annotation := annotation then
    if let `(source_native_type% ($_raw) ($native) via ($equiv)) := annotation then
      return ← `(source_native_type% ($(← valueTypeTerm type)) ($native) via ($equiv))
    if let `(source_native_type% ($_raw) ($native)) := annotation then
      return ← `(source_native_type% ($(← valueTypeTerm type)) ($native))
  return ← valueTypeTerm type

private def bindingNativeCoordinate (annotation : TSyntax `term) : Option NativeCoordinate :=
  match annotation with
  | `(source_native_type% ($_raw) ($native) via ($equiv)) => some ⟨native, equiv⟩
  | _ => none

private def lookupFunction (functions : Array Callee) (name : TSyntax `ident) : MacroM Callee := do
  let some fn := functions.find? (fun fn => fn.name.getId == name.getId)
    | Macro.throwErrorAt name s!"unknown source function '{name.getId}'; name a local function or a qualified imported function"
  return fn

private def parseBinding (functions : Array Callee)
    (scope : Scope) (stx : TSyntax `term) :
    MacroM (Ty × TSyntax `term × TSyntax `term) := do
  let (head, operands) := match stx with
    | `($head:term $operands:term*) => (head, operands)
    | _ => (stx, #[])
  if head.raw.getId == `NodeRef.cons &&
      !functions.any (fun fn => fn.name.getId == head.raw.getId) then
    unless operands.size == 2 do
      Macro.throwErrorAt stx "node construction expects a scalar head and an optional tail"
    let value ← parseAtom scope operands[0]!
    let kind : CellTy ← match value.type with
      | .nat => pure CellTy.nat
      | .bool => pure CellTy.bool
      | _ => Macro.throwErrorAt operands[0]! "node construction requires a Nat or Bool head"
    let tail ← parseAtom scope operands[1]!
    expectType operands[1]! tail.type (.option (.node kind))
    let kindTerm ← match kind with
      | CellTy.nat => `(Complexity.Language.CellTy.nat)
      | CellTy.bool => `(Complexity.Language.CellTy.bool)
    return (.node kind,
      ← `(Complexity.Language.Stmt.consNode (kind := $kindTerm) $(value.term) $(tail.term)),
      ← `(Complexity.Language.NodeRef.consM (kind := $kindTerm) $(value.value) $(tail.value)))
  if let some (receiver, field) := fieldAccess? head then
    if field == `read && !functions.any (fun fn => fn.name.getId == head.raw.getId) then
      unless operands.isEmpty do
        Macro.throwErrorAt stx "a node read takes no arguments"
      let (kind, ref) ← parseNodeRef scope receiver
      return (.prod kind.toTy (.option (.node kind)),
        ← `(Complexity.Language.Stmt.readNode $(ref.term)),
        ← `(Complexity.Language.NodeRef.readM $(ref.value)))
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

private partial def guardElements (condition : TSyntax `term) : MacroM (List (TSyntax `doElem)) :=
  match condition with
  | `(($inner:term)) => guardElements inner
  | `(do $body:doSeq) => pure (getDoElems body).toList
  | _ => do return [← `(doElem| return $condition)]

-- Normalize only the supported expression vocabulary. Fresh lexical names are
-- consumed by the ordinary typed translator and cannot capture user bindings.
private def normalizeBooleanBranch (stx : TSyntax `term)
    (condition yes no : NormalizedValue) : MacroM NormalizedValue := do
  let name ← freshProofName stx `boolean
  let initial ← `(doElem| let mut $name:ident : Bool := false)
  let yesBody := doSequence (yes.bindings.push (← `(doElem| $name:ident := $(yes.value))))
  let noBody := doSequence (no.bindings.push (← `(doElem| $name:ident := $(no.value))))
  let branch ← `(doElem| if $(condition.value) then $yesBody:doSeq else $noBody:doSeq)
  return ⟨condition.bindings ++ #[initial, branch], ⟨name.raw⟩, true⟩

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
    | `(source_native% ($raw) ($native) ($nativeType) via ($equiv)) => do
        let raw ← normalizeValue raw false expected
        let bindings ← raw.bindings.mapM fun binding => do
          match binding with
          | `(doElem| let $name:ident $[: $type:term]? := $value:term) =>
              `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($value))
          | _ => Macro.throwErrorAt binding "a native layout expansion must contain only primitive bindings"
        return { raw with
          bindings := bindings
          value := ← `(source_native% ($(raw.value)) ($native) ($nativeType) via ($equiv))
          atomic := false }
    | `(source_native% ($raw) ($native) ($nativeType)) => do
        let raw ← normalizeValue raw false expected
        let bindings ← raw.bindings.mapM fun binding => do
          match binding with
          | `(doElem| let $name:ident $[: $type:term]? := $value:term) =>
              `(doElem| let $name:ident $[: $type:term]? := source_raw_value% ($value))
          | _ => Macro.throwErrorAt binding "a native layout expansion must contain only primitive bindings"
        return { raw with
          bindings := bindings
          value := ← `(source_native% ($(raw.value)) ($native) ($nativeType))
          atomic := false }
    | `(source_raw_value% ($raw)) => do
        let raw ← normalizeValue raw false expected
        return { raw with value := ← `(source_raw_value% ($(raw.value))), atomic := false }
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
    | `($left > $right) => binary left right fun a b => `($a > $b)
    | `($left ≥ $right) => binary left right fun a b => `($a ≥ $b)
    | `($left >= $right) => binary left right fun a b => `($a >= $b)
    | `(!$value) => do
        let condition ← normalizeValue value true (some .bool)
        normalizeBooleanBranch stx condition ⟨#[], ← `(false), true⟩ ⟨#[], ← `(true), true⟩
    | `($left && $right) => do
        let condition ← normalizeValue left true (some .bool)
        let yes ← normalizeValue right false (some .bool)
        normalizeBooleanBranch stx condition yes ⟨#[], ← `(false), true⟩
    | `($left || $right) => do
        let condition ← normalizeValue left true (some .bool)
        let no ← normalizeValue right false (some .bool)
        normalizeBooleanBranch stx condition ⟨#[], ← `(true), true⟩ no
    | `($left != $right) | `($left ≠ $right) => do
        normalizeValue (← `(!($left == $right))) false expected
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

-- Operand bindings must enter the lexical scope before overloaded equality is
-- resolved. Boolean equality uses the existing typed branch/assignment core.
private partial def normalizeTypedValue (scope : Scope) (stx : TSyntax `term)
    (atomize : Bool) (expected : Option Ty := none) : MacroM NormalizedValue := do
  let normalized ← normalizeValue stx atomize expected
  if !normalized.bindings.isEmpty then
    return normalized
  match normalized.value with
  | `(($value:term : $type:term)) =>
      let value ← normalizeTypedValue scope value false (some (← parseType type))
      return { value with value := ← `(($(value.value) : $type)) }
  | `($left == $right) | `($left = $right) =>
      let lhs ← parseAtom scope left
      let rhs ← parseAtom scope right
      if lhs.type == .bool || rhs.type == .bool then
        expectType left lhs.type .bool
        expectType right rhs.type .bool
        let no ← normalizeValue (← `(!$right)) false (some .bool)
        normalizeBooleanBranch stx ⟨#[], left, true⟩ ⟨#[], right, true⟩ no
      else
        return normalized
  | _ => return normalized

private def normalizeCall (functions : Array Callee) (scope : Scope) (stx : TSyntax `term) :
    MacroM (Array (TSyntax `doElem) × TSyntax `term) := withRef stx do
  if let `($head:term $operands:term*) := stx then
    if head.raw.getId == `NodeRef.cons &&
        !functions.any (fun fn => fn.name.getId == head.raw.getId) then
      unless operands.size == 2 do
        Macro.throwErrorAt stx "node construction expects a scalar head and an optional tail"
      let value ← normalizeValue operands[0]! true
      -- Install the head's real primitive bindings before inferring its kind.
      -- The tail is normalized only afterwards, with its precise option type.
      if !value.bindings.isEmpty then
        return (value.bindings, Lean.Syntax.mkApp head #[value.value, operands[1]!])
      let valueAtom ← parseAtom scope value.value
      let kind : CellTy ← match valueAtom.type with
        | .nat => pure CellTy.nat
        | .bool => pure CellTy.bool
        | _ => Macro.throwErrorAt operands[0]! "node construction requires a Nat or Bool head"
      let tail ← normalizeValue operands[1]! true (some (.option (.node kind)))
      return (tail.bindings, Lean.Syntax.mkApp head #[value.value, tail.value])
  match stx with
  | `($head:term $operands:term*) =>
      let mut bindings := #[]
      let mut arguments := #[]
      let callee := functions.find? (fun fn => fn.name.getId == head.raw.getId)
      let mut head := head
      if callee.isNone then
        if let some (receiver, field) := fieldAccess? head then
          if field == `get || field == `set || field == `slice || field == `read then
            let normalized ← normalizeValue receiver true
            bindings := normalized.bindings
            head ← `($(normalized.value).$(mkIdent field):ident)
      for operand in operands, index in [:operands.size] do
        let expected := callee.bind fun fn => fn.params[index]?.map (·.type)
        let normalized ← normalizeValue operand true expected
        bindings := bindings ++ normalized.bindings
        arguments := arguments.push normalized.value
      return (bindings, Lean.Syntax.mkApp head arguments)
  | _ =>
      if let some (receiver, field) := fieldAccess? stx then
        if field == `read && !functions.any (fun fn => fn.name.getId == stx.raw.getId) then
          let normalized ← normalizeValue receiver true
          return (normalized.bindings,
            ← `($(normalized.value).$(mkIdent field):ident))
      return (#[], stx)

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

private def somePattern? (pattern : TSyntax `term) : Option (TSyntax `term) :=
  match pattern with
  | `(some $payload) | `(Option.some $payload) | `(.some $payload) => some payload
  | _ => none

private inductive BindingPattern where
  | wildcard
  | name (value : TSyntax `ident)
  | pair (left right : BindingPattern)
  | typed (pattern : BindingPattern) (type : Ty)

private instance : Nonempty BindingPattern := ⟨.wildcard⟩

private partial def parseBindingPattern (pattern : TSyntax `term) : MacroM BindingPattern := do
  match pattern with
  | `(_) => return .wildcard
  | `(($pattern:term : $type:term)) =>
      return .typed (← parseBindingPattern pattern) (← parseType type)
  | `(($pattern:term)) => parseBindingPattern pattern
  | `(($left, $right)) | `(Prod.mk $left $right) =>
      return .pair (← parseBindingPattern left) (← parseBindingPattern right)
  | `($name:ident) => return .name name
  | _ => Macro.throwErrorAt pattern "expected a name, _, or a nested product pattern"

private def BindingPattern.names : BindingPattern → List Name
  | .wildcard => []
  | .name binder => [binder.getId]
  | .pair left right => left.names ++ right.names
  | .typed pattern _ => pattern.names

private def checkedBindingPattern (pattern : TSyntax `term) : MacroM BindingPattern := do
  let parsed ← parseBindingPattern pattern
  unless parsed.names.Nodup do
    Macro.throwErrorAt pattern "a source pattern cannot bind the same name twice"
  return parsed

-- The value supplied here has already been evaluated once. Project only used
-- fields, sharing each nested product projection; even ignored patterns are
-- checked against their actual source type.
private def patternBindings (pattern : BindingPattern) (type : Ty)
    (value : TSyntax `term) : MacroM (Array (TSyntax `doElem)) := do
  match pattern with
  | .wildcard => return #[]
  | .name name =>
      return #[← `(doElem| let $name:ident : $(← valueTypeTerm type) := $value)]
  | .typed pattern expected =>
      expectType value type expected
      patternBindings pattern type value
  | .pair left right =>
      let .prod leftType rightType := type
        | Macro.throwErrorAt value "a product pattern requires a source product"
      let (bindings, base) ← if value.raw.isIdent then pure (#[], value) else do
        let name ← freshProofName value `pattern
        pure (#[← `(doElem| let $name:ident : $(← valueTypeTerm type) := $value)],
          (⟨name.raw⟩ : TSyntax `term))
      let leftBindings ← patternBindings left leftType (← `(Prod.fst $base))
      let rightBindings ← patternBindings right rightType (← `(Prod.snd $base))
      let fields := leftBindings ++ rightBindings
      return if fields.isEmpty then #[] else bindings ++ fields

private def normalizeElement (functions : Array Callee) (scope : Scope) (result : Ty)
    (element : TSyntax `doElem) :
    MacroM (Array (TSyntax `doElem) × TSyntax `doElem) := withRef element do
  if let some (value, first, firstBody, second, secondBody) := optionMatch? element then
    let normalized ← normalizeTypedValue scope value true
    return (normalized.bindings, ← `(doElem| match $(normalized.value):term with
      | $first:term => $firstBody:doSeq
      | $second:term => $secondBody:doSeq))
  match element with
  | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeTypedValue scope value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let mut $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeTypedValue scope value false (← annotation.mapM parseType)
      return (normalized.bindings,
        ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| let $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $pattern:term := $value:term) =>
      let normalized ← normalizeTypedValue scope value false
      if !normalized.bindings.isEmpty then
        return (normalized.bindings,
          ← `(doElem| let $pattern:term := $(normalized.value)))
      let pattern ← checkedBindingPattern pattern
      let parsed ← parsePrimitive scope normalized.value
      let name ← freshProofName value `pattern
      let initial ← `(doElem| let $name:ident : $(← valueTypeTerm parsed.type) := $(normalized.value))
      let expanded := #[initial] ++ (← patternBindings pattern parsed.type ⟨name.raw⟩)
      return (expanded.pop, expanded.back!)
  | `(doElem| let $pattern:term ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      if !bindings.isEmpty then
        return (bindings, ← `(doElem| let $pattern:term ← $action:term))
      let pattern ← checkedBindingPattern pattern
      let (type, _, _) ← parseBinding functions scope action
      let name ← freshProofName action `pattern
      let initial ← `(doElem| let $name:ident ← $action:term)
      let expanded := #[initial] ++ (← patternBindings pattern type ⟨name.raw⟩)
      return (expanded.pop, expanded.back!)
  | `(doElem| $name:ident := $value:term) =>
      let (binding, _) ← lookupBinding scope name
      let normalized ← normalizeTypedValue scope value false (some binding.type)
      return (normalized.bindings, ← `(doElem| $name:ident := $(normalized.value)))
  | `(doElem| $name:ident ← $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| $name:ident ← $action:term))
  | `(doElem| return $value:term) =>
      let normalized ← normalizeTypedValue scope value false (some result)
      return (normalized.bindings, ← `(doElem| return $(normalized.value)))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let normalized ← normalizeTypedValue scope condition false
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| if $condition:term then $yes:doSeq) =>
      let normalized ← normalizeTypedValue scope condition false
      let no := doSequence #[]
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| while $_condition do $_body) => return (#[], element)
  | `(doElem| with_scratch do $_body:doSeq) => return (#[], element)
  | `(doElem| $action:term) =>
      let (bindings, action) ← normalizeCall functions scope action
      return (bindings, ← `(doElem| $action:term))
  | _ => return (#[], element)

private partial def stableRangeBound (scope : Scope) (value : TSyntax `term)
    (allowLength : Bool := true) : MacroM Bool := do
  match value with
  | `(source_native% ($raw) ($_native) ($_type) via ($_equiv)) =>
      stableRangeBound scope raw allowLength
  | `(source_native% ($raw) ($_native) ($_type)) =>
      stableRangeBound scope raw allowLength
  | `(($value:term)) => stableRangeBound scope value allowLength
  | `($_:num) => return true
  | _ =>
      if let some (receiver, field) := fieldAccess? value then
        if allowLength && field == `length then
          if let `($name:ident) := receiver then
            let (binding, _) ← lookupBinding scope name
            return !binding.isMutable && match binding.type with
              | .buffer _ => true
              | _ => false
        return false
      if let `($name:ident) := value then
        let (binding, _) ← lookupBinding scope name
        return !binding.isMutable && binding.type == .nat
      return false

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
        | none => Macro.throwErrorAt second "expected a 'some pattern' option branch"
      else if nonePattern second then
        match somePattern? first with
        | some payload => pure (secondBody, payload, firstBody)
        | none => Macro.throwErrorAt first "expected a 'some pattern' option branch"
      else Macro.throwErrorAt element "an option match needs exactly none and some branches"
    let option ← parseAtom scope value
    let .option payloadType := option.type
      | Macro.throwErrorAt value "source matching currently supports Option values"
    let pattern ← checkedBindingPattern payload
    let payloadName ← freshProofName payload `payload
    let (sourceName, bindings) ← match pattern with
      | .name name => pure (name.getId, #[])
      | _ => do
          pure (payloadName.getId, ← patternBindings pattern payloadType ⟨payloadName.raw⟩)
    let noneCode ← recurse scope result (getDoElems noneBody).toList nextIndex
    let someCode ← recurse (⟨some sourceName, payloadName, payloadType, false, none⟩ :: scope)
      result (bindings.toList ++ (getDoElems someBody).toList) (nextIndex + noneCode.sites.size)
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
        else ⟨none, saved, Ty.bool, false, none⟩ :: scope
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
      let site : BlockSite := ⟨name, scope, result, some guardCode.term, bodyCode.term, none, none⟩
      let code := loopMember site "Code"
      return ⟨⟨code.raw⟩, ← loopProofBody site, true,
        guardCode.sites ++ bodyCode.sites |>.push site⟩
  | `(doElem| source_range% ($cursor:ident, $stop:term, $stride:term) do $body:doSeq) =>
      let name := generatedName family owner s!"_loop{nextIndex}"
      let condition ← `($cursor:ident < $stop)
      let guardCode ← recurse scope .bool (← guardElements condition) (nextIndex + 1)
      let bodyCode ← recurse scope result (getDoElems body).toList
        (nextIndex + 1 + guardCode.sites.size)
      let (cursorBinding, _) ← lookupBinding scope cursor
      let stopValue ← parsePrimitive scope stop (some .nat)
      let strideValue ← parsePrimitive scope stride (some .nat)
      let metadata : FiniteRange :=
        ⟨cursorBinding.proofName, stopValue.value, strideValue.value,
          bodyCode.proofBody, bodyCode.fallsThrough⟩
      let site : BlockSite :=
        ⟨name, scope, result, some guardCode.term, bodyCode.term, some metadata, none⟩
      let code := loopMember site "Code"
      let positive ← freshProofName element `positiveStep
      let checked ← `(doElem| have $positive:ident : 0 < $(strideValue.value) := by
        simp (config := { zetaDelta := true, failIfUnchanged := false }) only
          [Nat.add_eq] <;> omega)
      return ⟨⟨code.raw⟩, #[checked] ++ (← loopProofBody site), true,
        guardCode.sites ++ bodyCode.sites |>.push site⟩
  | `(doElem| for $pattern:term in $collection:term do $body:doSeq) =>
      let isRange := match collection with
        | `([ : $_stop]) | `([ $_start : $_stop ]) |
          `([ : $_stop : $_stride ]) | `([ $_start : $_stop : $_stride ]) => true
        | _ => false
      let cursorName := if isRange then match pattern with
          | `($name:ident) => name.getId.eraseMacroScopes
          | _ => `index
        else `index
      let cursor ← freshProofName element cursorName
      let limit ← freshProofName element `stop
      let stepName ← freshProofName element `step
      let rangeInitial (start stop stride : TSyntax `term) := do
        let cursorBinding ← `(doElem| let mut $cursor:ident : Nat := $start)
        let (initial, stop) ← if ← stableRangeBound scope stop then
            pure (#[cursorBinding], stop)
          else
            pure (#[cursorBinding, ← `(doElem| let $limit:ident : Nat := $stop)],
              (⟨limit.raw⟩ : TSyntax `term))
        if ← stableRangeBound scope stride false then
          pure (initial, stop, stride)
        else
          pure (initial.push (← `(doElem| let $stepName:ident : Nat := $stride)), stop,
            (⟨stepName.raw⟩ : TSyntax `term))
      let (initial, stop, stride, elementBinding) ← match collection with
        | `([ : $stop]) => do
            let (initial, stop, stride) ← rangeInitial (← `(0)) stop (← `(1))
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ $start : $stop ]) => do
            let (initial, stop, stride) ← rangeInitial start stop (← `(1))
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ : $stop : $stride ]) => do
            let (initial, stop, stride) ← rangeInitial (← `(0)) stop stride
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | `([ $start : $stop : $stride ]) => do
            let (initial, stop, stride) ← rangeInitial start stop stride
            pure (initial, stop, stride,
              ← `(doElem| let $pattern:term := $cursor:ident))
        | _ => do
            let buffer ← freshProofName collection `buffer
            pure (#[← `(doElem| let $buffer:ident := $collection),
              ← `(doElem| let $limit:ident : Nat := ($buffer:ident).length),
              ← `(doElem| let mut $cursor:ident : Nat := 0)],
              (⟨limit.raw⟩ : TSyntax `term), ← `(1),
              ← `(doElem| let $pattern:term ← ($buffer:ident).get $cursor:ident))
      let advance ← `(doElem| $cursor:ident := $cursor:ident + $stride)
      let iteration := doSequence (#[elementBinding] ++ getDoElems body ++ #[advance])
      let loop ← `(doElem| source_range% ($cursor:ident, $stop, $stride) do $iteration:doSeq)
      recurse scope result (initial.toList ++ [loop]) nextIndex
  | `(doElem| with_scratch do $body:doSeq) =>
      let name := generatedName family owner s!"_scope{nextIndex}"
      let bodyCode ← recurse scope result (getDoElems body).toList (nextIndex + 1)
      let site : BlockSite := ⟨name, scope, result, none, bodyCode.term, none, none⟩
      let code := loopMember site "Code"
      -- The observation exposes Control rather than a syntactically terminal
      -- return. Retain its normal continuation just as for a named loop.
      return ⟨⟨code.raw⟩, ← loopProofBody site, true,
        bodyCode.sites.push site⟩
  | `(doElem| $action:term) => actionCode functions scope action
  | _ =>
      Macro.throwErrorAt element
        "unsupported source statement; use let, let mut, assignment, a named call, buffer access or allocation, node read or construction, with_scratch, if/then/else, Option match, while, bounded for, or return"

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
          let type ← bindingValueType parsed.type annotation (some parsed.value)
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, true, bindingNativeCoordinate type⟩ :: scope)
            result rest nextIndex
          let binding ← `(doElem| let mut $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value (← annotation.mapM parseType)
          checkAnnotation annotation parsed.type
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType parsed.type annotation (some parsed.value)
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, parsed.type, false, bindingNativeCoordinate type⟩ :: scope)
            result rest nextIndex
          let binding ← `(doElem| let $proofName:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType bindingType annotation
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, true, bindingNativeCoordinate type⟩ :: scope)
            result rest nextIndex
          let binding ← `(doElem| let mut $proofName:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough, body.sites⟩
      | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding functions scope action
          checkAnnotation annotation bindingType
          let proofName ← freshProofName name name.getId
          let type ← bindingValueType bindingType annotation
          let body ← blockCode family functions owner
            (⟨some name.getId, proofName, bindingType, false, bindingNativeCoordinate type⟩ :: scope)
            result rest nextIndex
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
      let scope : Scope := fn.params.toList.zipIdx.map fun (param, index) =>
        ⟨some param.name.getId, param.name, param.type, false,
          fn.nativeView.map fun view => ⟨view.parameterTypes[index]!, view.parameterEquivs[index]!⟩⟩
      let result ← blockCode family functions fn.name scope fn.result (getDoElems body).toList 1
      return { result with sites := result.sites.map fun site =>
        { site with nativeResult := fn.nativeView.map fun view => ⟨view.resultType, view.resultEquiv⟩ } }
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
          ($view:ident).symm $values:ident = $restored := by
        apply ($view:ident).injective
        simp only [Equiv.apply_symm_apply, $viewApply:ident,
          Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there] <;>
          (symm; exact $(← tupleExtProof site.scope)))).raw]
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
  let captureViewSymmApply := loopMember site "captureView_symm_apply"
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
      $captureView:ident $entry:ident = $projected := rfl)).raw,
    (← `(command| /-- Restore grouped locals using the checked coordinate projection laws. -/
      theorem $captureViewSymmApply:ident ($grouped:ident : $mutable:ident × $captured:ident) :
          ($captureView:ident).symm $grouped:ident = ($view:ident).symm $restored := by
        simp only [$captureView:ident, Equiv.symm_trans_apply, $regroupSymmApply:ident])).raw]

private def hasNativeCoordinates (site : BlockSite) : Bool :=
  site.nativeResult.isSome || site.scope.any (·.native.isSome)

private def loopNativeCaptureDeclarations (site : BlockSite) : MacroM (Array Syntax) := do
  unless hasNativeCoordinates site do return #[]
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let mutable := loopMember site "NativeMutable"
  let captured := loopMember site "NativeCaptured"
  let view := loopMember site "NativeCaptureView"
  let viewApply := loopMember site "native_captureView_apply"
  let symmApply := loopMember site "native_captureView_symm_apply"
  let rawView := loopMember site "CaptureView"
  let rawViewApply := loopMember site "captureView_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let viewSymm := loopMember site "view_symm_apply"
  let types ← scopeTypes site.scope
  let coordinate ← `(Equiv.prodCongr $(← scopeNativeEquiv mutableScope)
    $(← scopeNativeEquiv capturedScope))
  let entry ← freshProofName site.name `entry
  let mut entryFields := #[]
  for (binding, index) in site.scope.zipIdx do
    let field ← `(Complexity.Language.Env.get $entry:ident $(← variableTerm index))
    entryFields := entryFields.push (← decodeNativeField binding field)
  let (mutableEntries, capturedEntries) := splitScopeFields site.scope entryFields
  let projected ← `(($(← fieldsTuple mutableEntries), $(← fieldsTuple capturedEntries)))
  let grouped ← freshProofName site.name `grouped
  let fields := mergeScopeFields site.scope
    (← tupleFields mutableScope (← `(($grouped:ident).1)))
    (← tupleFields capturedScope (← `(($grouped:ident).2)))
  let encoded ← encodeNativeFields site.scope fields
  let mut restored ← `(Complexity.Language.Env.empty)
  for (binding, field) in (site.scope.toArray.zip encoded).reverse do
    restored ← `(Complexity.Language.Env.cons (τ := $(← typeTerm binding.type)) $field $restored)
  return #[
    (← `(command| /-- Mutable loop coordinates in their registered native types. -/
      abbrev $mutable:ident := $(← scopeNativeTypes mutableScope))).raw,
    (← `(command| /-- Immutable captures in their registered native types. -/
      abbrev $captured:ident := $(← scopeNativeTypes capturedScope))).raw,
    (← `(command| /-- A native view of the same environment, with no runtime conversion. -/
      def $view:ident : Complexity.Language.Env $types ≃ ($mutable:ident × $captured:ident) :=
        ($rawView:ident).trans ($coordinate).symm)).raw,
    (← `(command| /-- Observe native loop coordinates without unfolding registered equivalences. -/
      theorem $viewApply:ident ($entry:ident : Complexity.Language.Env $types) :
          $view:ident $entry:ident = $projected := by
        simp only [$view:ident, Equiv.trans_apply, Equiv.prodCongr_symm,
          Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Prod.map,
          $rawViewApply:ident])).raw,
    (← `(command| /-- Restore native loop coordinates without unfolding equivalence proofs. -/
      theorem $symmApply:ident ($grouped:ident : $mutable:ident × $captured:ident) :
          ($view:ident).symm $grouped:ident = $restored := by
        simp only [$view:ident, $rawView:ident, Equiv.symm_trans_apply, Equiv.symm_symm,
          Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map, $regroupSymm:ident,
          $viewSymm:ident])).raw]

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
      [("guard_preservesCaptures", "Guard", Ty.bool),
       ("body_preservesCaptures", "Body", site.result),
       ("preservesCaptures", "Code", site.result)] do
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
    if hasNativeCoordinates site then
      let nativeName := loopMember site ("native_" ++ suffix)
      let nativeView := loopMember site "NativeCaptureView"
      let capturedEquiv ← scopeNativeEquiv (site.scope.filter (! ·.isMutable))
      declarations := declarations.push (← `(command|
        /-- The same actual exit preserves its native immutable captures. -/
        theorem $nativeName:ident {$entry:ident $finish:ident : Complexity.Language.State $types}
            {$control:ident : Complexity.Language.Control $result}
            ($execution:ident : Complexity.Language.Exec $program:ident $code:ident
              $entry:ident $finish:ident $control:ident) :
            ($nativeView:ident ($finish:ident).locals).2 =
              ($nativeView:ident ($entry:ident).locals).2 :=
          congrArg (fun captures => ($capturedEquiv).symm captures) ($name:ident $execution:ident))).raw
  return declarations

private def loopNativeContractDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  unless hasNativeCoordinates site do return #[]
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutable := loopMember site "NativeMutable"
  let captured := loopMember site "NativeCaptured"
  let view := loopMember site "NativeCaptureView"
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let pre ← freshProofName site.name `pre
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let afterFields ← tupleFields mutableScope (← `(($after:ident).1))
  let app (name : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨name.raw⟩ arguments
  let preType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let normalType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyNativeScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let rawPre ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap) =>
    $(app pre (beforeFields.push ⟨heap.raw⟩)))
  let rawNormal ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap)
    ($after:ident : $mutable:ident × $captured:ident) ($finish:ident : Complexity.Language.Heap) =>
    $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let captures ← scopeTuple capturedScope
  let mut declarations := #[]
  for (suffix, codeSuffix, result) in
      [("native_guard_contract", "Guard", Ty.bool),
       ("native_body_contract", "Body", site.result),
       ("native_contract", "Code", site.result)] do
    let name := loopMember site suffix
    let code := loopMember site codeSuffix
    let rawResult ← valueTypeTerm result
    let nativeResult := if codeSuffix == "Guard" then none else site.nativeResult
    let resultType ← match nativeResult with
      | some native => pure native.type
      | none => pure rawResult
    let decoded ← match nativeResult with
      | some native => `(($(native.equiv)).symm $value:ident)
      | none => pure (⟨value.raw⟩ : TSyntax `term)
    let returnedType ← quantifyNativeScope mutableScope (← `(Complexity.Language.Heap →
      $resultType → $(← quantifyNativeScope afterScope (← `(Complexity.Language.Heap → Prop)))))
    let rawReturned ← `(fun ($before:ident : $mutable:ident) ($heap:ident : Complexity.Language.Heap)
      ($value:ident : $rawResult) ($after:ident : $mutable:ident × $captured:ident)
      ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (beforeFields ++ #[⟨heap.raw⟩, decoded] ++ afterFields ++ #[⟨finish.raw⟩])))
    let type ← quantifyNativeScope capturedScope (← `($preType → $normalType → $returnedType → Prop))
    let definition ← curryNativeScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident =>
      Complexity.Language.Stmt.BlockSpec
        (fun ($before:ident : $mutable:ident) =>
          Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
            ($before:ident, $captures)) $rawPre $rawNormal $rawReturned))
    declarations := declarations.push (← `(command|
      /-- The actual block contract with native mutable parameters and fixed captures.
      Only the returned predicate decodes the source value; control and both heaps stay unchanged. -/
      abbrev $name:ident : $type := $definition)).raw
  return declarations

private def loopContractDeclarations (program : TSyntax `ident) (site : BlockSite) :
    MacroM (Array Syntax) := do
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutableType := loopMember site "Mutable"
  let capturedType := loopMember site "Captured"
  let localsType := loopMember site "Locals"
  let captureView := loopMember site "CaptureView"
  let captures ← scopeTuple capturedScope
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let current ← freshProofName site.name `current
  let value ← freshProofName site.name `value
  let pre ← freshProofName site.name `pre
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let mutableAfterFields ← tupleFields mutableScope ⟨after.raw⟩
  let afterFields ← tupleFields mutableScope (← `(($after:ident).1))
  let nativeAfterFields := (splitScopeFields site.scope
    (← tupleFields site.scope ⟨after.raw⟩)).1
  let sourceBefore := mutableScope.toArray.map fun binding => (⟨binding.proofName.raw⟩ : TSyntax `term)
  let app (name : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨name.raw⟩ arguments
  let preType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let normalType ← quantifyScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let rawPre ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) => $(app pre (beforeFields.push ⟨heap.raw⟩)))
  let rawNormal ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap)
    ($after:ident : $mutableType:ident × $capturedType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let mutableNormal ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (beforeFields ++ #[⟨heap.raw⟩] ++ mutableAfterFields ++ #[⟨finish.raw⟩])))
  let mut declarations := #[]
  for (suffix, observationSuffix, codeSuffix, result) in
      [("guard_contract", "guard", "Guard", Ty.bool),
       ("body_contract", "body", "Body", site.result),
       ("contract", "", "Code", site.result)] do
    let name := loopMember site suffix
    let iffName := loopMember site (suffix ++ "_iff")
    let observation := if observationSuffix.isEmpty then site.name
      else loopMember site observationSuffix
    let observed := loopMember site
      (if observationSuffix.isEmpty then "observe" else observationSuffix ++ "_observe")
    let code := loopMember site codeSuffix
    let resultType ← typeTerm result
    let result ← valueTypeTerm result
    let returnedType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → $result →
      $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
    let rawReturned ← `(fun ($before:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) ($value:ident : $result)
      ($after:ident : $mutableType:ident × $capturedType:ident)
      ($finish:ident : Complexity.Language.Heap) =>
        $(app returned (beforeFields ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          afterFields ++ #[⟨finish.raw⟩])))
    let mutableReturned ← `(fun ($before:ident : $mutableType:ident)
      ($heap:ident : Complexity.Language.Heap) ($value:ident : $result)
      ($after:ident : $mutableType:ident) ($finish:ident : Complexity.Language.Heap) =>
        $(app returned (beforeFields ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          mutableAfterFields ++ #[⟨finish.raw⟩])))
    let type ← quantifyScope capturedScope
      (← `($preType → $normalType → $returnedType → Prop))
    let definition ← curryScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident =>
      Complexity.Language.Stmt.BlockSpec
        (fun ($before:ident : $mutableType:ident) =>
          Complexity.Language.Stmt.observe $captureView:ident $code:ident $program:ident
            ($before:ident, $captures)) $rawPre $rawNormal $rawReturned))
    declarations := declarations.push (← `(command|
      /-- Relational total correctness with ordinary mutable parameters and fixed captures.
      The existing block contract retains both actual heaps and excludes faults. -/
      abbrev $name:ident : $type := $definition)).raw
    let contract := app name
      ((capturedScope.toArray.map fun binding => ⟨binding.proofName.raw⟩) ++
        #[⟨pre.raw⟩, ⟨normal.raw⟩, ⟨returned.raw⟩])
    let normalPost := app normal (sourceBefore ++ #[⟨heap.raw⟩] ++
      nativeAfterFields ++ #[⟨finish.raw⟩])
    let returnedPost := app returned (sourceBefore ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
      nativeAfterFields ++ #[⟨finish.raw⟩])
    let ordinary ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
      $(app pre (sourceBefore.push ⟨heap.raw⟩)) →
      Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
        $(scopeApplication site.scope observation)
        (fun $current:ident => ⟨$current:ident = $heap:ident⟩)
        (fun outcome $finish:ident => ⟨match outcome.1 with
          | .normal => let $after:ident : $localsType:ident := outcome.2; $normalPost
          | .returned $value:ident =>
              let $after:ident : $localsType:ident := outcome.2; $returnedPost
          | .fault _ => False⟩, ⟨⟩)))
    let iffType ← quantifyScope capturedScope (← `(∀ ($pre:ident : $preType)
      ($normal:ident : $normalType) ($returned:ident : $returnedType), $contract ↔ $ordinary))
    let regroup := loopMember site "regroup_apply"
    let regroupSymm := loopMember site "regroup_symm_apply"
    let outcome ← freshProofName site.name `outcome
    -- The generic and declaration-specialized matches have distinct motives.
    -- Compare only their actual control branches, leaving the action opaque.
    let postProof ← `(by
      apply Iff.of_eq
      congr 1
      apply Prod.ext
      · funext $outcome:ident $finish:ident
        rcases $outcome:ident with ⟨control, locals⟩
        cases control <;> rfl
      · rfl)
    -- `Prod.forall` also exposes a product-valued individual binding. Expand
    -- exactly those source types, stopping before the opaque Triple itself.
    let rec productCongr (type : Ty) (proof : TSyntax `term) : MacroM (TSyntax `term) := do
      match type with
      | .prod left right => productCongr left (← productCongr right proof)
      | _ =>
          let parameter ← freshProofName site.name `mutableField
          `(forall_congr' (fun ($parameter:ident : $(← valueTypeTerm type)) => $proof))
    let mut matchProof ← `(forall_congr' (fun ($heap:ident : Complexity.Language.Heap) =>
      imp_congr_right (fun _ => $postProof)))
    for binding in mutableScope.reverse do
      matchProof ← productCongr binding.type matchProof
    let proof ← curryScope capturedScope (← `(fun $pre:ident $normal:ident $returned:ident => by
      simp only [$name:ident, $captureView:ident, Complexity.Language.Stmt.observe_reindex]
      simp only [Complexity.Language.Stmt.BlockSpec.map_iff]
      simp only [$observed:ident, $regroup:ident, $regroupSymm:ident,
        Complexity.Language.Stmt.BlockSpec,
        $mutableType:ident, Prod.forall, forall_const]
      exact $matchProof))
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Introduce named mutable variables directly, without unpacking internal coordinates. -/
      theorem $iffName:ident : $iffType := $proof)).raw
    let specName := loopMember site
      (if observationSuffix.isEmpty then "spec" else observationSuffix ++ "_spec")
    let frame := loopMember site
      (if observationSuffix.isEmpty then "preservesCaptures"
       else observationSuffix ++ "_preservesCaptures")
    let view := loopMember site "View"
    let regroupName := loopMember site "Regroup"
    let specification ← freshProofName site.name `specification
    let post ← freshProofName site.name `post
    let postType ← `(Std.Do.PostCond
      (Complexity.Language.Control $resultType × $localsType:ident)
      (.arg Complexity.Language.Heap .pure))
    let finalValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
    let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
    let finalLocals ← fieldsTuple (mergeScopeFields site.scope finalValues capturedValues)
    let normalConsequence ← quantifyScope afterScope
      (← `(∀ ($finish:ident : Complexity.Language.Heap),
        $(app normal (sourceBefore ++ #[⟨heap.raw⟩] ++ finalValues ++ #[⟨finish.raw⟩])) →
        (($post:ident).1 (.normal, $finalLocals) $finish:ident).down))
    let returnedConsequenceBody ← quantifyScope afterScope
      (← `(∀ ($finish:ident : Complexity.Language.Heap),
        $(app returned (sourceBefore ++ #[⟨heap.raw⟩, ⟨value.raw⟩] ++
          finalValues ++ #[⟨finish.raw⟩])) →
        (($post:ident).1 (.returned $value:ident, $finalLocals) $finish:ident).down))
    let returnedConsequence ← `(∀ ($value:ident : $result), $returnedConsequenceBody)
    let nativeSpec ← quantifyScope mutableScope (← `(∀ ($post:ident : $postType),
      Std.Do.Triple (m := StateT Complexity.Language.Heap Part) (ps := .arg _ .pure)
        $(scopeApplication site.scope observation)
        (fun $heap:ident => ⟨$(app pre (sourceBefore.push ⟨heap.raw⟩)) ∧
          $normalConsequence ∧ $returnedConsequence⟩) $post:ident))
    let specType ← quantifyScope capturedScope (← `(∀ {$pre:ident : $preType}
      {$normal:ident : $normalType} {$returned:ident : $returnedType}
      ($specification:ident : $contract), $nativeSpec))
    let specProof ← curryScope mutableScope (← `(fun $post:ident => by
      simpa only [$regroupSymm:ident, $observed:ident, Prod.forall, forall_const] using
        Complexity.Language.Stmt.observe_fixed_spec $view:ident $regroupName:ident
          $program:ident $code:ident $frame:ident $captures
          (pre := $rawPre) (normal := $mutableNormal) (returned := $mutableReturned)
          $specification:ident
          $(← scopeTuple mutableScope) $post:ident))
    let specProof ← curryScope capturedScope
      (← `(fun {$pre:ident} {$normal:ident} {$returned:ident} $specification:ident => $specProof))
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Apply a chosen mathematical contract to the native block action.
      Continuations see ordinary mutable outputs; proved frames restore the fixed captures. -/
      theorem $specName:ident : $specType := $specProof)).raw
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

private def loopIndependentContractDeclaration (program : TSyntax `ident) (site : BlockSite)
    (wellFoundedMode : Bool) : MacroM Syntax := do
  let name := loopMember site
    (if wellFoundedMode then "wellFounded_contract" else "variant_contract")
  let mutableScope := site.scope.filter (·.isMutable)
  let capturedScope := site.scope.filter (! ·.isMutable)
  let afterScope := (← freshMutableScope site "after_").filter (·.isMutable)
  let mutableType := loopMember site "Mutable"
  let captureView := loopMember site "CaptureView"
  let invariant ← freshProofName site.name `invariant
  let progress ← freshProofName site.name (if wellFoundedMode then `relation else `variant)
  let wellFounded ← freshProofName site.name `wellFounded
  let ready ← freshProofName site.name `ready
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let guardSpec ← freshProofName site.name `guardSpec
  let bodySpec ← freshProofName site.name `bodySpec
  let before ← freshProofName site.name `before
  let after ← freshProofName site.name `after
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let again ← freshProofName site.name `again
  let initial ← freshProofName site.name `initial
  let captures ← scopeTuple capturedScope
  let capturedValues := capturedScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let beforeValues := mutableScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let afterValues := afterScope.toArray.map fun b => (⟨b.proofName.raw⟩ : TSyntax `term)
  let app (function : TSyntax `ident) (arguments : Array (TSyntax `term)) :=
    Lean.Syntax.mkApp ⟨function.raw⟩ arguments
  let contract (suffix : String) (pre normal returned : TSyntax `term) :=
    app (loopMember site suffix) (capturedValues ++ #[pre, normal, returned])
  let ignoreStart (body : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut result ← `(fun _ => $body)
    for _ in mutableScope do result ← `(fun _ => $result)
    return result
  let predicateType ← quantifyScope mutableScope (← `(Complexity.Language.Heap → Prop))
  let readyType ← quantifyScope mutableScope (← `(Complexity.Language.Heap →
    $(← quantifyScope afterScope (← `(Complexity.Language.Heap → Prop)))))
  let result ← valueTypeTerm site.result
  let returnedType ← `($result → $predicateType)
  let progressType ← if wellFoundedMode then
      `(($mutableType:ident × Complexity.Language.Heap) →
        ($mutableType:ident × Complexity.Language.Heap) → Prop)
    else quantifyScope mutableScope (← `(Complexity.Language.Heap → Nat))
  let falseNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) => False)))
  let guardReturned ← curryScope mutableScope
    (← `(fun ($heap:ident : Complexity.Language.Heap) ($again:ident : Bool) =>
      $(← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
        if $again:ident then
          $(app ready (beforeValues ++ #[⟨heap.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩]))
        else $(app normal (afterValues.push ⟨finish.raw⟩)))))))
  let guardType := contract "guard_contract" ⟨invariant.raw⟩ falseNormal guardReturned
  let decrease ← if wellFoundedMode then
      `($progress:ident ($(← scopeTuple afterScope), $finish:ident)
        ($(← scopeTuple mutableScope), $heap:ident))
    else
      `($(app progress (afterValues.push ⟨finish.raw⟩)) <
        $(app progress (beforeValues.push ⟨heap.raw⟩)))
  let bodyNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app invariant (afterValues.push ⟨finish.raw⟩)) ∧ $decrease)))
  let finalReturnedBody ← curryScope afterScope
    (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterValues ++ #[⟨finish.raw⟩]))))
  let finalReturned ← ignoreStart (← `(fun ($value:ident : $result) => $finalReturnedBody))
  let bodyType ← quantifyScope mutableScope (← `(∀ ($heap:ident : Complexity.Language.Heap),
    $(app invariant (beforeValues.push ⟨heap.raw⟩)) →
    $(contract "body_contract" (app ready (beforeValues.push ⟨heap.raw⟩))
      bodyNormal finalReturned)))
  let finalNormal ← ignoreStart
    (← curryScope afterScope (← `(fun ($finish:ident : Complexity.Language.Heap) =>
      $(app normal (afterValues.push ⟨finish.raw⟩)))))
  let conclusion := contract "contract" ⟨invariant.raw⟩ finalNormal finalReturned
  let mut type ← `(∀ ($ready:ident : $readyType) ($normal:ident : $predicateType)
    ($returned:ident : $returnedType) ($guardSpec:ident : $guardType)
    ($bodySpec:ident : $bodyType), $conclusion)
  if wellFoundedMode then
    type ← `(∀ ($wellFounded:ident : WellFounded $progress:ident), $type)
  type ← quantifyScope capturedScope (← `(∀ ($invariant:ident : $predicateType)
    ($progress:ident : $progressType), $type))
  let beforeFields ← tupleFields mutableScope ⟨before.raw⟩
  let afterFields ← tupleFields mutableScope ⟨after.raw⟩
  let rawPredicate (predicate : TSyntax `ident) :=
    `(fun ($before:ident : $mutableType:ident) ($heap:ident : Complexity.Language.Heap) =>
      $(app predicate (beforeFields.push ⟨heap.raw⟩)))
  let rawReady ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app ready (beforeFields ++ #[⟨heap.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let rawReturned ← `(fun ($value:ident : $result) ($after:ident : $mutableType:ident)
    ($finish:ident : Complexity.Language.Heap) =>
      $(app returned (#[⟨value.raw⟩] ++ afterFields ++ #[⟨finish.raw⟩])))
  let rawBody ← `(fun ($before:ident : $mutableType:ident)
    ($heap:ident : Complexity.Language.Heap) $initial:ident =>
      $(app bodySpec (beforeFields ++ #[⟨heap.raw⟩, ⟨initial.raw⟩])))
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardFrame := loopMember site "guard_preservesCaptures"
  let bodyFrame := loopMember site "body_preservesCaptures"
  let specification ← if wellFoundedMode then
      `(Complexity.Language.Stmt.observe_while_fixed_contract
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $(← rawPredicate invariant)
        $progress:ident $wellFounded:ident $rawReady $(← rawPredicate normal)
        $rawReturned $guardSpec:ident $rawBody)
    else
      `(Complexity.Language.Stmt.observe_while_fixed_variant_contract
        $captureView:ident $program:ident $guard:ident $body:ident
        $guardFrame:ident $bodyFrame:ident $captures $(← rawPredicate invariant)
        $(← rawPredicate progress) $rawReady $(← rawPredicate normal)
        $rawReturned $guardSpec:ident $rawBody)
  let mut proof ← `(fun $ready:ident $normal:ident $returned:ident
    $guardSpec:ident $bodySpec:ident => $specification)
  if wellFoundedMode then proof ← `(fun $wellFounded:ident => $proof)
  proof ← curryScope capturedScope (← `(fun $invariant:ident $progress:ident => $proof))
  return (← `(command|
    /-- Prove a named loop from independent mathematical guard and body contracts.
    Actual guard effects and early body returns are retained; only normal iterations decrease. -/
    theorem $name:ident : $type := $proof)).raw

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
  let nestedSites := sites.filter fun other =>
    other.name.getId != site.name.getId &&
      (site.body.raw.hasIdent (loopMember other "Code").getId ||
        site.guard.any (fun guard => guard.raw.hasIdent (loopMember other "Code").getId))
  let expandedFolds ← nestedSites.mapM fun other => do
    return (other, ← freshProofName other.name `nestedObservation)
  let expandedFoldArgs ← namedSimpArgs (expandedFolds.map (·.2))
  let viewDefinitions ← namedSimpArgs ((#[site] ++ nestedSites).map fun other =>
    loopMember other "View")
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
    ``Complexity.Language.Stmt.observe_readNode, ``Complexity.Language.Stmt.observe_consNode,
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
    -- Ordinary blocks normalize through the proved projection equations. Only
    -- actual nested blocks need their composed and named views aligned below.
    let initialProof ← if nestedSites.isEmpty then `(source_conversion% $applied =>
        unfold $name:ident
        simp (config := { implicitDefEqProofs := false }) only [$allArgs,*]
        dsimp only [Complexity.Language.Env.equivProd, Complexity.Language.Env.equivUnit,
          Equiv.symm]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [Equiv.coe_fn_mk, Complexity.Language.Env.cons_here,
            Complexity.Language.Env.cons_there, Complexity.Language.Env.head_cons,
            Complexity.Language.Env.tail_cons, Complexity.Language.Env.get_tail])
    else `(source_conversion% $applied =>
        unfold $name:ident
        simp (config := { implicitDefEqProofs := false }) only [$allArgs,*]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [$viewDefinitions,*]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [$expandedFoldArgs,*]
        dsimp only [Complexity.Language.Env.equivProd, Complexity.Language.Env.equivUnit,
          Equiv.symm]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [Equiv.coe_fn_mk, Complexity.Language.Env.cons_here,
            Complexity.Language.Env.cons_there, Complexity.Language.Env.head_cons,
            Complexity.Language.Env.tail_cons, Complexity.Language.Env.get_tail])
    let mut proof := initialProof
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
  let proof ← curryScope site.scope (← `(source_conversion% $applied =>
      unfold $name:ident
      rw [$loopCode:ident, $composition:ident]
      simp only [$foldNames,*]))
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
          let ($control:ident, $locals:ident) ← MonadLift.monadLift $invocation
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
    ``Complexity.Language.Stmt.evalWith_readNode, ``Complexity.Language.Stmt.evalWith_consNode,
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
  | .buffer _ | .node _ => false
  | .prod left right => pureValueType left && pureValueType right
  | .option value => pureValueType value

-- These identifiers were resolved by the source parser, and local proof
-- variables have fresh names. Replacing them cannot capture a source binder.
private def pureProofElements (body : LoweredBlock) : Array (TSyntax `doElem) :=
  body.proofBody ++ body.sites.flatMap fun site =>
    site.finiteRange.map (·.body) |>.getD #[]

private def rangeMutableScope (site : BlockSite) : Scope :=
  (site.scope.filter (·.isMutable)).drop 1

private def nativeMarkedValue (value : TSyntax `term) : MacroM (TSyntax `term) := do
  let value ← value.raw.replaceM fun node => do
    match node with
    | `(source_native% ($_raw) ($native) ($_nativeType) via ($_equiv)) => return some native.raw
    | `(source_native% ($_raw) ($native) ($_nativeType)) => return some native.raw
    | `(source_native_type% ($_raw) ($native) via ($_equiv)) => return some native.raw
    | `(source_native_type% ($_raw) ($native)) => return some native.raw
    | _ => return none
  return ⟨value⟩

mutual

private partial def nativeRangeStep (callees : Array Callee) (sites : Array BlockSite)
    (site : BlockSite) : MacroM (TSyntax `term) := do
  let some range := site.finiteRange
    | Macro.throwErrorAt site.name "expected a finite source range"
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
  let some range := site.finiteRange
    | Macro.throwErrorAt site.name "expected a finite source range"
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

private partial def nativeRangeValue (callees : Array Callee) (sites : Array BlockSite)
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
private def pureFunctionOrder (family : TSyntax `ident) (functions : Array Function)
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

private def nativeDeclaration (family : TSyntax `ident) (fn : Function)
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

private def nativeRangeCorrespondenceDeclarations (program : TSyntax `ident)
    (callees : Array Callee) (sites : Array BlockSite) (site : BlockSite)
    (nativeResult : NativeCoordinate) (nativeSimplifications : Array (TSyntax `ident)) :
    MacroM (Array Syntax) := do
  let some range := site.finiteRange
    | Macro.throwErrorAt site.name "expected a finite source range"
  let name := loopMember site "eq_pure"
  let nativeName := loopMember site "eq_pure_native"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let regroup := loopMember site "regroup_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let code := loopMember site "Code"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardObserved := loopMember site "guard_observe"
  let bodyObserved := loopMember site "body_observe"
  let guardEquation := loopMember site "guard_eq"
  let bodyObservation := loopMember site "body"
  let nativeGuardEquation := loopMember site "native_guard_eq"
  let nativeBodyTransport := loopMember site "native_body_eq_of_eq"
  let nativeBodyEquation := loopMember site "native_body_eq"
  let nativeCaptured := loopMember site "NativeCaptured"
  let nativeRangeStop := loopMember site "nativeRangeStop"
  let nativeRangeStride := loopMember site "nativeRangeStep"
  let nativeBodyStep := loopMember site "nativeBodyStep"
  let resultType ← typeTerm site.result
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeNativeTypes mutableScope
  let capturedScope := site.scope.filter (! ·.isMutable)
  let captures ← scopeTuple capturedScope
  let capturedFields ← encodeNativeFields capturedScope (capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term))
  let nativeCaptureView := loopMember site "NativeCaptureView"
  let index ← freshProofName site.name `index
  let mutable ← freshProofName site.name `mutable
  let outcome ← freshProofName site.name `outcome
  let value ← freshProofName site.name `value
  let next ← freshProofName site.name `nextMutable
  let groupedCaptures ← freshProofName site.name `captures
  let groupedFields ← tupleFields capturedScope ⟨groupedCaptures.raw⟩
  let bindCaptures (term : TSyntax `term) : MacroM (TSyntax `term) := do
    let mut term := term
    for (binding, field) in (capturedScope.toArray.zip groupedFields).reverse do
      if term.raw.hasIdent binding.proofName.getId then
        term ← `(let $(binding.proofName):ident : $(← bindingNativeType binding) := $field; $term)
    return term
  let groupedStop ← bindCaptures (← nativeMarkedValue range.stop)
  let groupedStride ← bindCaptures (← nativeMarkedValue range.stride)
  let tupleEta ← freshProofName site.name `mutableTupleEta
  let bodyPure ← freshProofName site.name `bodyPure
  let positive ← freshProofName site.name `positiveStep
  let tupleEtaRules := if mutableScope.isEmpty then #[] else #[tupleEta]
  let tupleEtaArgs ← namedSimpArgs tupleEtaRules
  let guardTupleEta ← if mutableScope.isEmpty then `(tactic| cases $mutable:ident) else do
    let rebuilt ← fieldsTuple (← tupleFields mutableScope ⟨mutable.raw⟩)
    `(tactic| have $tupleEta:ident : $rebuilt = $mutable:ident := $(← tupleExtProof mutableScope))
  let bodyTupleEta ← if mutableScope.isEmpty then `(tactic| cases $next:ident) else do
    let rebuilt ← fieldsTuple (← tupleFields mutableScope ⟨next.raw⟩)
    `(tactic| have $tupleEta:ident : $rebuilt = $next:ident := $(← tupleExtProof mutableScope))
  let step ← nativeRangeStep callees sites site
  let groupedStep ← bindCaptures step
  let initial ← scopeTuple mutableScope
  let inputFields ← encodeNativeFields mutableScope
    (← tupleFields mutableScope ⟨mutable.raw⟩)
  let bodyInvocation := Lean.Syntax.mkApp ⟨bodyObservation.raw⟩
    (mergeScopeFields site.scope (#[⟨index.raw⟩] ++ inputFields) capturedFields)
  let outputFields ← encodeNativeFields mutableScope
    (← tupleFields mutableScope (← `(($outcome:ident).2)))
  let normalLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[← `($index:ident + $(range.stride))] ++ outputFields) capturedFields)
  let returnedLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[⟨index.raw⟩] ++ outputFields) capturedFields)
  let encode ← `(($(nativeResult.equiv)).toFun)
  let bodyPremise ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) → $bodyInvocation =
      (let $outcome:ident := ($step:term) $index:ident $mutable:ident
       pure (match ($outcome:ident).1 with
         | none => (Complexity.Language.Control.normal, $normalLocals)
         | some $value:ident =>
             (Complexity.Language.Control.returned ($encode $value:ident), $returnedLocals))))
  let nativeGuardType ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $guard:ident $program:ident
      (($index:ident, $mutable:ident), $captures) =
      pure (Complexity.Language.Control.returned (decide ($index:ident < $(range.stop))),
        (($index:ident, $mutable:ident), $captures)))
  let nativeBodyType ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) →
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $body:ident $program:ident
      (($index:ident, $mutable:ident), $captures) =
      pure (match ($step:term) $index:ident $mutable:ident with
        | (none, $next:ident) => (Complexity.Language.Control.normal,
            (($index:ident + $(range.stride), $next:ident), $captures))
        | (some $value:ident, $next:ident) =>
            (Complexity.Language.Control.returned ($encode $value:ident),
              (($index:ident, $next:ident), $captures))))
  let groupedGuardType ← `(∀ ($groupedCaptures:ident : $nativeCaptured:ident)
    ($index:ident : Nat) ($mutable:ident : $mutableType),
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $guard:ident $program:ident
      (($index:ident, $mutable:ident), $groupedCaptures:ident) =
      pure (Complexity.Language.Control.returned
        (decide ($index:ident < $nativeRangeStop:ident $groupedCaptures:ident)),
        (($index:ident, $mutable:ident), $groupedCaptures:ident)))
  let groupedBodyType ← `(∀ ($groupedCaptures:ident : $nativeCaptured:ident)
    ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $nativeRangeStop:ident $groupedCaptures:ident →
    Complexity.Language.Stmt.observe $nativeCaptureView:ident $body:ident $program:ident
      (($index:ident, $mutable:ident), $groupedCaptures:ident) =
      pure (match $nativeBodyStep:ident $groupedCaptures:ident $index:ident $mutable:ident with
        | (none, $next:ident) => (Complexity.Language.Control.normal,
            (($index:ident + $nativeRangeStride:ident $groupedCaptures:ident, $next:ident),
              $groupedCaptures:ident))
        | (some $value:ident, $next:ident) =>
            (Complexity.Language.Control.returned ($encode $value:ident),
              (($index:ident, $next:ident), $groupedCaptures:ident))))
  let groupedProof (type proof : TSyntax `term) : MacroM (TSyntax `term) := do
    let checked ← freshProofName site.name `checked
    let capturedEta ← freshProofName site.name `capturedTupleEta
    let rebuilt ← fieldsTuple groupedFields
    let applied := Lean.Syntax.mkApp ⟨checked.raw⟩ groupedFields
    `(by
      intro $groupedCaptures:ident
      have $checked:ident : $(← quantifyNativeScope capturedScope type) := $proof
      have $capturedEta:ident : $rebuilt = $groupedCaptures:ident := $(← tupleExtProof capturedScope)
      simpa only [$nativeRangeStop:ident, $nativeRangeStride:ident, $nativeBodyStep:ident, $capturedEta:ident,
        Equiv.refl_symm, Equiv.refl_apply] using $applied)
  let nativeGuardProof ← `(by
    intro $index:ident $mutable:ident
    $guardTupleEta:tactic
    simp only [$nativeCaptureView:ident, Complexity.Language.Stmt.observe_reindex, $captureView:ident,
      $guardObserved:ident, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map]
    simp only [$guardEquation:ident, map_pure, $regroup:ident,
      Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_apply_apply, Prod.map, Prod.mk.eta, $tupleEtaArgs,*])
  let nativeBodyProof ← `(fun $bodyPure:ident => by
    intro $index:ident $mutable:ident inside
    simp only [$nativeCaptureView:ident, Complexity.Language.Stmt.observe_reindex, $captureView:ident,
      $bodyObserved:ident, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map]
    simp only [Equiv.refl_apply] at $bodyPure:ident
    rw [$bodyPure:ident $index:ident $mutable:ident inside]
    cases stepEq : ($step:term) $index:ident $mutable:ident with
    | mk returned $next:ident =>
        $bodyTupleEta:tactic
        cases returned <;> simp only [stepEq, map_pure, $regroup:ident,
          Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.refl_apply,
          Equiv.symm_apply_apply, Prod.map, Prod.mk.eta, $tupleEtaArgs,*])
  let capturedArguments := capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term)
  let guardApplication := Lean.Syntax.mkApp ⟨nativeGuardEquation.raw⟩ #[captures]
  let bodyTransportApplication := Lean.Syntax.mkApp ⟨nativeBodyTransport.raw⟩ capturedArguments
  let priorSites := sites.takeWhile (fun other => other.name.getId != site.name.getId)
  let bodyElements := range.body ++ priorSites.flatMap fun other =>
    other.finiteRange.map (·.body) |>.getD #[]
  let dependencies := callees.filter fun callee =>
    bodyElements.any (fun element => element.raw.hasIdent callee.observation.getId)
  let equations ← dependencies.mapM fun callee => do
    let some equation := callee.pureEquation
      | Macro.throwErrorAt callee.name "a pure source callee must have a correspondence theorem"
    return equation
  let equations := equations ++ nativeSimplifications
  let loopRules := priorSites.map fun other => loopMember other "eq_pure"
  let bodyRules := sites.map fun other => loopMember other "body_eq"
  let nativeBodyEquationProof ← curryNativeScope capturedScope (← `(by
    apply $bodyTransportApplication
    source_pure_block_correspondence [$equations:ident,*]
      ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*]))
  let native ← nativeRangeValue callees sites site (some ⟨positive.raw⟩)
  let actualArguments ← encodeNativeFields site.scope (site.scope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term))
  let actualInvocation := Lean.Syntax.mkApp ⟨site.name.raw⟩ actualArguments
  let actualLocals ← fieldsTuple actualArguments
  let finalLocals ← fieldsTuple (← encodeNativeFields site.scope
    (← tupleFields site.scope (← `(($outcome:ident).2))))
  let observedResult ← `(let $outcome:ident := $native
     pure ((($outcome:ident).1.elim
       (Complexity.Language.Control.normal (result := $resultType))
       (fun value => Complexity.Language.Control.returned (result := $resultType) ($encode value))),
       $finalLocals))
  let conclusion ← `($actualInvocation = $observedResult)
  let unquantified ← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $conclusion)
  let mut nativeType := unquantified
  let mut nativeProof ← `(fun $positive:ident $bodyPure:ident => by
    have actual := Complexity.Language.Stmt.observe_while_eq_forIn_range_step_encoded
      $nativeCaptureView:ident $program:ident $guard:ident $body:ident $captures
      $(range.stop) $(range.stride) $positive:ident $encode $step
      $guardApplication ($bodyTransportApplication $bodyPure:ident)
      $(range.cursor):ident $initial
    change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $actualLocals = _
    rw [$code:ident]
    funext heap
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    have execution := Complexity.Language.Stmt.observe_eq_some_iff.mp (congrFun actual heap)
    simpa only [$nativeCaptureView:ident, $captureView:ident, Equiv.symm_trans_apply, $regroupSymm:ident,
      Equiv.symm_symm, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.refl_apply, Prod.map] using execution)
  for binding in site.scope.reverse do
    let type ← bindingNativeType binding
    nativeType ← `(∀ ($(binding.proofName):ident : $type), $nativeType)
    nativeProof ← `(fun ($(binding.proofName):ident : $type) => $nativeProof)
  -- Quantify raw coordinates for reliable rewriting at arbitrary source locals.
  -- The checked inverse is used only in this theorem, never in source execution.
  let mut rawScope : Scope := []
  let mut decodedArguments : Array (TSyntax `term) := #[]
  for binding in site.scope do
    let raw ← freshProofName site.name binding.proofName.getId
    rawScope := rawScope ++ [{ binding with proofName := raw, native := none }]
    decodedArguments := decodedArguments.push (← decodeNativeField binding ⟨raw.raw⟩)
  -- A rewrite rule must expose the raw invocation itself, not an
  -- encode/decode round trip around metavariables that rewriting cannot infer.
  let rawConclusion ← `($(scopeApplication rawScope site.name) = $observedResult)
  let mut rawType ← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $rawConclusion)
  for (binding, decoded) in (site.scope.toArray.zip decodedArguments).reverse do
    rawType ← `(let $(binding.proofName):ident : $(← bindingNativeType binding) := $decoded; $rawType)
  rawType ← quantifyScope rawScope rawType
  let nativeApplication := Lean.Syntax.mkApp ⟨nativeName.raw⟩ decodedArguments
  let rawProof ← curryScope rawScope (← `(by
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply, Equiv.refl_symm]
      using $nativeApplication))
  return #[
    (← `(command|
      /-- The actual fixed range endpoint selected from this loop's native captures. -/
      def $nativeRangeStop:ident ($groupedCaptures:ident : $nativeCaptured:ident) : Nat :=
        $groupedStop)).raw,
    (← `(command|
      /-- The actual fixed stride selected from this loop's native captures. -/
      def $nativeRangeStride:ident ($groupedCaptures:ident : $nativeCaptured:ident) : Nat :=
        $groupedStride)).raw,
    (← `(command|
      /-- The generated pure single-step view, with native mutable values and possible early return.
      Naming this view adds neither a source operation nor a separate user-written implementation. -/
      def $nativeBodyStep:ident ($groupedCaptures:ident : $nativeCaptured:ident) :
          Nat → $mutableType → Option $(nativeResult.type) × $mutableType := $groupedStep)).raw,
    (← `(command|
      /-- The actual guard observed at native mutable locals and fixed captures. -/
      theorem $nativeGuardEquation:ident : $groupedGuardType :=
        $(← groupedProof nativeGuardType (← curryNativeScope capturedScope nativeGuardProof)))).raw,
    (← `(command|
      /-- Transport the same body equation into native locals, retaining actual early returns. -/
      theorem $nativeBodyTransport:ident :
          $(← quantifyNativeScope capturedScope (← `($bodyPremise → $nativeBodyType))) :=
        $(← curryNativeScope capturedScope nativeBodyProof))).raw,
    (← `(command|
      /-- The same source body in native locals, using the already proved callee correspondences.
      Its result keeps normal continuation and early return distinct and preserves the heap. -/
      theorem $nativeBodyEquation:ident : $groupedBodyType :=
        $(← groupedProof nativeBodyType nativeBodyEquationProof))).raw,
    (← `(command|
      /-- The existing source range in checked native local coordinates. Encoding
      changes neither its iterations, early exits, heap nor source operation costs. -/
      theorem $nativeName:ident : $nativeType := $nativeProof)).raw,
    (← `(command|
      /-- The same range correspondence at arbitrary raw locals, reconstructed
      through the registered lossless native coordinates for theorem composition. -/
      theorem $name:ident : $rawType := $rawProof)).raw]

private def rangeCorrespondenceDeclarations (program : TSyntax `ident)
    (callees : Array Callee) (sites : Array BlockSite) (site : BlockSite)
    (nativeSimplifications : Array (TSyntax `ident)) : MacroM Syntax := do
  if let some native := site.nativeResult then
    return mkNullNode
      (← nativeRangeCorrespondenceDeclarations program callees sites site native nativeSimplifications)
  let some range := site.finiteRange
    | Macro.throwErrorAt site.name "expected a finite source range"
  let name := loopMember site "eq_pure"
  let view := loopMember site "View"
  let captureView := loopMember site "CaptureView"
  let regroup := loopMember site "regroup_apply"
  let regroupSymm := loopMember site "regroup_symm_apply"
  let code := loopMember site "Code"
  let guard := loopMember site "Guard"
  let body := loopMember site "Body"
  let guardObserved := loopMember site "guard_observe"
  let bodyObserved := loopMember site "body_observe"
  let guardEquation := loopMember site "guard_eq"
  let bodyObservation := loopMember site "body"
  let resultType ← typeTerm site.result
  let mutableScope := rangeMutableScope site
  let mutableType ← scopeValueTypes mutableScope
  let capturedScope := site.scope.filter (! ·.isMutable)
  let captures ← scopeTuple capturedScope
  let capturedFields := capturedScope.toArray.map fun binding =>
    (⟨binding.proofName.raw⟩ : TSyntax `term)
  let index ← freshProofName site.name `index
  let mutable ← freshProofName site.name `mutable
  let outcome ← freshProofName site.name `outcome
  let value ← freshProofName site.name `value
  let bodyPure ← freshProofName site.name `bodyPure
  let positive ← freshProofName site.name `positiveStep
  let step ← nativeRangeStep callees sites site
  let initial ← scopeTuple mutableScope
  let inputFields ← tupleFields mutableScope ⟨mutable.raw⟩
  let bodyInvocation := Lean.Syntax.mkApp ⟨bodyObservation.raw⟩
    (mergeScopeFields site.scope (#[⟨index.raw⟩] ++ inputFields) capturedFields)
  let outputFields ← tupleFields mutableScope (← `(($outcome:ident).2))
  let normalLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[← `($index:ident + $(range.stride))] ++ outputFields) capturedFields)
  let returnedLocals ← fieldsTuple (mergeScopeFields site.scope
    (#[⟨index.raw⟩] ++ outputFields) capturedFields)
  let bodyPremise ← `(∀ ($index:ident : Nat) ($mutable:ident : $mutableType),
    $index:ident < $(range.stop) → $bodyInvocation =
      (let $outcome:ident := ($step:term) $index:ident $mutable:ident
       pure (match ($outcome:ident).1 with
         | none => (Complexity.Language.Control.normal, $normalLocals)
         | some $value:ident => (Complexity.Language.Control.returned $value:ident, $returnedLocals))))
  let native ← nativeRangeValue callees sites site (some ⟨positive.raw⟩)
  let conclusion ← `($(scopeApplication site.scope site.name) =
    (let $outcome:ident := $native
     pure ((($outcome:ident).1.elim
       (Complexity.Language.Control.normal (result := $resultType))
       (Complexity.Language.Control.returned (result := $resultType))),
       ($outcome:ident).2)))
  let type ← quantifyScope site.scope
    (← `(∀ ($positive:ident : 0 < $(range.stride)), $bodyPremise → $conclusion))
  let proof ← curryScope site.scope (← `(fun $positive:ident $bodyPure:ident => by
    have actual := Complexity.Language.Stmt.observe_while_eq_forIn_range_step
      $captureView:ident $program:ident $guard:ident $body:ident $captures
      $(range.stop) $(range.stride) $positive:ident $step
      (by
        intro $index:ident $mutable:ident
        simp only [$captureView:ident, Complexity.Language.Stmt.observe_reindex,
          $guardObserved:ident, $regroupSymm:ident]
        simp [$guardEquation:ident, $regroup:ident])
      (by
        intro $index:ident $mutable:ident inside
        simp only [$captureView:ident, Complexity.Language.Stmt.observe_reindex,
          $bodyObserved:ident, $regroupSymm:ident]
        rw [$bodyPure:ident $index:ident $mutable:ident inside]
        cases stepEq : ($step:term) $index:ident $mutable:ident with
        | mk returned next =>
            cases returned <;> simp only [stepEq, map_pure, $regroup:ident] <;> rfl)
      $(range.cursor):ident $initial
    change Complexity.Language.Stmt.observe $view:ident $code:ident $program:ident
      $(← scopeTuple site.scope) = _
    rw [$code:ident]
    funext heap
    apply Complexity.Language.Stmt.observe_eq_some_iff.mpr
    have execution := Complexity.Language.Stmt.observe_eq_some_iff.mp (congrFun actual heap)
    simpa only [$captureView:ident, Equiv.symm_trans_apply, $regroupSymm:ident] using execution))
  return (← `(command|
    /-- Finite iteration correspondence, with its one-body obligation left in
    the enclosing function's callee and recursive-hypothesis scope. -/
    theorem $name:ident : $type := $proof)).raw

private def pureCorrespondenceDeclaration (family : TSyntax `ident) (fn : Function)
    (callees : Array Callee) (body : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name "_action_eq_pure"
  let action := actionName family fn.name true
  let equation := generatedName family fn.name "_action_eq"
  let native := generatedName family fn.name ""
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let actualArguments := match fn.nativeView with
    | none => arguments
    | some view => (view.parameterEncodings.zip arguments).map fun (encode, argument) =>
        Lean.Syntax.mkApp encode #[argument]
  let actual := Lean.Syntax.mkApp ⟨action.raw⟩ actualArguments
  let value := Lean.Syntax.mkApp ⟨native.raw⟩ arguments
  let encodedValue := match fn.nativeView with
    | none => value
    | some view => Lean.Syntax.mkApp view.resultEncoding #[value]
  let result ← valueTypeTerm fn.result
  let dependencies := callees.filter fun callee =>
    callee.observation.getId != action.getId &&
      (pureProofElements body).any (fun element => element.raw.hasIdent callee.observation.getId)
  let equations ← dependencies.mapM fun callee => do
    let some equation := callee.pureEquation
      | Macro.throwErrorAt callee.name "a pure source callee must have a correspondence theorem"
    return equation
  let loopRules := body.sites.map fun site => loopMember site "eq_pure"
  let bodyRules := body.sites.map fun site => loopMember site "body_eq"
  let mut type ← `($actual = (pure $encodedValue : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let baseProof : TSyntax `term ← match fn.nativeView with
    | none => `(by
        source_pure_correspondence $value using $equation:ident [$equations:ident,*]
          ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*])
    | some view => `(by
        source_pure_correspondence $value using $equation:ident [$equations:ident,*]
          encodings% [$(view.simplifications):ident,*]
          ranges% [$loopRules:ident,*] blocks% [$bodyRules:ident,*])
  let mut proof := baseProof
  for (param, index) in fn.params.zipIdx.reverse do
    let parameter := param.name
    let parameterType ← match fn.nativeView with
      | none => valueTypeTerm param.type
      | some view => pure view.parameterTypes[index]!
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    /-- The actual source action terminates with the generated native result and
    preserves every initial heap. Lean's native recursion principle proves this once. -/
    theorem $name:ident : $type := $proof)).raw

private def pureRawCorrespondenceDeclaration (family : TSyntax `ident)
    (fn : Function) (view : NativeView) : MacroM Syntax := do
  let name := generatedName family fn.name "_action_eq_pure_raw"
  let action := actionName family fn.name true
  let correspondence := generatedName family fn.name "_action_eq_pure"
  let native := generatedName family fn.name ""
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let rebuilt := (view.parameterRebuilds.zip arguments).map fun (rebuild, argument) =>
    Lean.Syntax.mkApp rebuild #[argument]
  let actual := Lean.Syntax.mkApp ⟨action.raw⟩ arguments
  let value := Lean.Syntax.mkApp view.resultEncoding
    #[Lean.Syntax.mkApp ⟨native.raw⟩ rebuilt]
  let result ← valueTypeTerm fn.result
  let mut type ← `($actual = (pure $value : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof := Lean.Syntax.mkApp ⟨correspondence.raw⟩ rebuilt
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    /-- Observe any raw layout through its checked native reconstruction.
    Reconstruction is proof-side transport, not an additional source operation. -/
    theorem $name:ident : $type := $proof)).raw

private def pureTotalDeclaration (family program : TSyntax `ident)
    (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_total"
  let native := generatedName family fn.name ""
  let observed := generatedName family fn.name "_observe"
  let correspondence := generatedName family fn.name
    (if fn.nativeView.isSome then "_action_eq_pure_raw" else "_action_eq_pure")
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
  let nativeValues := match fn.nativeView with
    | none => values
    | some view => (view.parameterRebuilds.zip values).map fun (rebuild, value) =>
        Lean.Syntax.mkApp rebuild #[value]
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ nativeValues
  let value := match fn.nativeView with
    | none => nativeValue
    | some view => Lean.Syntax.mkApp view.resultEncoding #[nativeValue]
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

private def nativeInputType : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `(Unit)
  | [type] => pure type
  | type :: rest => do `($type × $(← nativeInputType rest))

private def nativeInputFields (count : Nat) (input : TSyntax `term) :
    MacroM (Array (TSyntax `term)) := do
  let mut fields := #[]
  let mut rest := input
  for index in [:count] do
    if index + 1 < count then
      fields := fields.push (← `(Prod.fst $rest))
      rest ← `(Prod.snd $rest)
    else
      fields := fields.push rest
  return fields

private def nativeRefinementDeclarations (family program : TSyntax `ident)
    (fn : Function) (view : NativeView) : MacroM (Array Syntax) := do
  let inputName := generatedName family fn.name "_inputEmbedding"
  let representation := generatedName family fn.name "_representation"
  let refinement := generatedName family fn.name "_refines"
  let arguments := generatedName family fn.name "_args"
  let native := generatedName family fn.name ""
  let observed := generatedName family fn.name "_observe"
  let correspondence := generatedName family fn.name "_action_eq_pure"
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let result ← typeTerm fn.result
  let inputType ← nativeInputType view.parameterTypes.toList
  let input ← freshProofName fn.name `input
  let left ← freshProofName fn.name `left
  let right ← freshProofName fn.name `right
  let same ← freshProofName fn.name `same
  let raw ← freshProofName fn.name `arguments
  let fields ← nativeInputFields fn.params.size ⟨input.raw⟩
  let encodedFields := (view.parameterEncodings.zip fields).map fun (encode, field) =>
    Lean.Syntax.mkApp encode #[field]
  let rawArguments := Lean.Syntax.mkApp ⟨arguments.raw⟩ encodedFields
  let nativeValue := Lean.Syntax.mkApp ⟨native.raw⟩ fields
  let encodedValue := Lean.Syntax.mkApp view.resultEncoding #[nativeValue]
  let mut rawRest ← `($raw:ident)
  let mut equalities := #[]
  for embedding in view.parameterEmbeddings do
    let projection ← `(fun ($raw:ident : Complexity.Language.Env $params) =>
      Complexity.Language.Env.head $rawRest)
    equalities := equalities.push (← `(Function.Embedding.injective $embedding
      (congrArg $projection $same:ident)))
    rawRest ← `(Complexity.Language.Env.tail $rawRest)
  let mut injectivity ← `(Subsingleton.elim $left:ident $right:ident)
  for (equality, index) in equalities.zipIdx.reverse do
    injectivity ← if index + 1 == equalities.size then pure equality
      else `(Prod.ext $equality $injectivity)
  let inputDeclaration ← `(command|
    /-- Canonical proof-side encoding of this function's native arguments.
    It does not insert an uncharged runtime conversion. -/
    def $inputName:ident : $inputType ↪ Complexity.Language.Env $params where
      toFun $input:ident := $rawArguments
      inj' $left:ident $right:ident $same:ident := $injectivity)
  let resultEmbedding := view.resultEmbedding
  let output ← `(fun (_ : $inputType) => $resultEmbedding)
  let model ← `(fun ($input:ident : $inputType) => $nativeValue)
  let representationDeclaration ← `(command|
    /-- Native mathematical arguments and results of this actual source function. -/
    def $representation:ident : Complexity.Language.FunctionRepresentation
        $inputType (fun _ => $(view.resultType))
        { params := $params, result := $result } :=
      Complexity.Language.FunctionRepresentation.ofEmbedding $inputName:ident $output)
  let refinementDeclaration ← `(command|
    /-- The generated ordinary native function describes this same source body. -/
    theorem $refinement:ident : Complexity.Language.RepresentedFunction.Refines
        $program:ident $id:ident $representation:ident (fun _ => True) $model := by
      change Complexity.Language.RepresentedFunction.Refines $program:ident $id:ident
        (Complexity.Language.FunctionRepresentation.ofEmbedding $inputName:ident $output)
        (fun _ => True) $model
      apply Complexity.Language.RepresentedFunction.Refines.of_encoded_eq_pure
        (program := $program:ident) (fn := $id:ident) (pre := fun _ => True)
        $inputName:ident $output $model
      intro $input:ident _
      change Complexity.Language.Program.eval $program:ident $id:ident $rawArguments =
        pure $encodedValue
      rw [$observed:ident]
      exact $(Lean.Syntax.mkApp ⟨correspondence.raw⟩ fields))
  return #[inputDeclaration.raw, representationDeclaration.raw, refinementDeclaration.raw]

private def programDeclarations (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) (imports : Array ImportedProgram)
    (pureMode : Bool) (nativeViews : Array NativeView := #[]) :
    MacroM (Syntax × Array FunctionInfo × Array LoopCoordinateRegistration) := do
  let mut functions : Array Function := #[]
  for source in sources do
    let fn ← parseFunction source
    let fn := { fn with nativeView := nativeViews.find? (fun view => view.header.name.getId == fn.name.getId) }
    if functions.any (fun previous => previous.name.getId == fn.name.getId) then
      Macro.throwErrorAt fn.name "duplicate source function name"
    if pureMode then
      unless pureValueType fn.result && fn.params.all (pureValueType ·.type) do
        Macro.throwErrorAt fn.name
          "pure source functions support Nat, Bool, Unit and their products/options, but no nested buffers or node references"
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
      if pureMode then some (generatedName family fn.name "") else none,
      if pureMode then some (generatedName family fn.name
        (if fn.nativeView.isSome then "_action_eq_pure_raw" else "_action_eq_pure")) else none⟩
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
          if fn.pure then some (mkCIdent (entry.source.family ++ fn.name)) else none,
          if fn.pure then some (mkCIdent (entry.source.family ++
            Name.mkSimple (fn.name.toString ++
              if fn.nativeHeader.isSome then "_action_eq_pure_raw" else "_action_eq_pure"))) else none⟩
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
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.readNode then
      Macro.throwErrorAt fn.name
        "node reading is effectful and is not supported by 'source_program (pure)'"
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.consNode then
      Macro.throwErrorAt fn.name
        "node construction is effectful and is not supported by 'source_program (pure)'"
    if pureMode then
      if body.sites.any (fun site => site.guard.isNone) then
        Macro.throwErrorAt fn.name
          "scratch allocation scopes are effectful and are not supported by 'source_program (pure)'"
      if body.sites.any (fun site => site.finiteRange.isNone) then
        Macro.throwErrorAt fn.name
          "pure source loops must be finite ranges; unbounded while is not supported"
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
      declarations := declarations ++ (← loopNativeCaptureDeclarations site)
  for site in loopSites do
    declarations := declarations ++ (← loopEquationDeclarations site loopSites calleeFolds)
    declarations := declarations.push (← loopContinuationDeclaration programName site loopSites)
    if site.guard.isSome then
      declarations := declarations ++ (← loopCaptureFrameDeclarations programName site loopSites)
      declarations := declarations ++ (← loopContractDeclarations programName site)
      declarations := declarations ++ (← loopNativeContractDeclarations programName site)
      declarations := declarations.push (← loopIndependentContractDeclaration programName site false)
      declarations := declarations.push (← loopIndependentContractDeclaration programName site true)
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
      for site in body.sites do
        declarations := declarations.push
          (← rangeCorrespondenceDeclarations programName callees body.sites site
            (fn.nativeView.map (·.simplifications) |>.getD #[]))
      declarations := declarations.push
        (← pureCorrespondenceDeclaration family fn callees body)
      match fn.nativeView with
      | none => declarations := declarations.push (← pureTotalDeclaration family programName fn)
      | some view =>
          declarations := declarations.push (← pureRawCorrespondenceDeclaration family fn view)
          declarations := declarations.push (← pureTotalDeclaration family programName fn)
          declarations := declarations ++ (← nativeRefinementDeclarations family programName fn view)
  let mut coordinates : Array LoopCoordinateRegistration := #[]
  for site in loopSites do
    if site.guard.isSome then
      let mut rules := #["view_apply", "view_symm_apply", "captureView_apply",
        "captureView_symm_apply", "regroup_apply", "regroup_symm_apply"].map
        (loopMember site)
      if hasNativeCoordinates site then
        rules := rules ++ #[loopMember site "native_captureView_apply",
          loopMember site "native_captureView_symm_apply"]
      if pureMode && site.nativeResult.isSome && site.finiteRange.isSome then
        rules := rules ++ #[loopMember site "nativeRangeStop", loopMember site "nativeRangeStep"]
      let nativeTypes := site.scope.toArray.filterMap (fun binding => binding.native.map (·.type))
      coordinates := coordinates.push {
        code := loopMember site "Code", rules := rules, nativeTypes := nativeTypes
      }
  return (mkNullNode declarations, (functions.map fun fn =>
    ⟨fn.name.getId, fn.params.map (fun param => (param.name.getId, param.type)), fn.result,
      pureMode, fn.nativeView.map (·.header)⟩), coordinates)

private def nativeExprSyntax (value : Lean.Expr) : Lean.Elab.Term.TermElabM (TSyntax `term) :=
  Lean.withOptions (fun options => options.setBool `pp.fullNames true) do
    Lean.PrettyPrinter.delab value

private partial def registeredTypeNames (type : Lean.Expr) : Lean.Meta.MetaM (Array Name) := do
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

private def registerLoopCoordinates (entries : Array LoopCoordinateRegistration) :
    Lean.Elab.Command.CommandElabM Unit := do
  for entry in entries do
    let code ← Lean.resolveGlobalConstNoOverload entry.code
    let mut rules ← entry.rules.mapM (fun rule => Lean.resolveGlobalConstNoOverload rule)
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
    modifyEnv fun env => loopCoordinatesExt.addEntry env (code, ⟨rules⟩)

private def nativeView (header : NativeHeader) : Lean.Elab.Term.TermElabM NativeView := do
  let mut simplifications := #[``Function.Embedding.coe_refl, ``Function.Embedding.coe_prodMap,
    ``Prod.map, ``id, ``Equiv.refl_apply, ``Equiv.refl_symm,
    ``Equiv.toFun_as_coe, ``Equiv.invFun_as_coe]
  for parameter in header.params do
    simplifications := simplifications ++ (← registeredTypeNames parameter.type.nativeType)
  simplifications := simplifications ++ (← registeredTypeNames header.result.nativeType)
  return {
    header := header
    parameterTypes := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.nativeType)
    resultType := ← nativeExprSyntax header.result.nativeType
    parameterEncodings := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.encoding)
    parameterRebuilds := ← header.params.mapM (fun parameter => do
      let rebuild ← nativeExprSyntax (← nativeReconstruction parameter.type)
      let rawType ← Lean.Elab.liftMacroM (valueTypeTerm parameter.type.coreTy)
      let nativeType ← nativeExprSyntax parameter.type.nativeType
      `(($rebuild : $rawType → $nativeType)))
    resultEncoding := ← nativeExprSyntax header.result.encoding
    parameterEmbeddings := ← header.params.mapM (fun parameter => nativeExprSyntax parameter.type.embedding)
    resultEmbedding := ← nativeExprSyntax header.result.embedding
    parameterEquivs := ← header.params.mapM (fun parameter => nativeEquivalence parameter.type)
    resultEquiv := ← nativeEquivalence header.result
    simplifications := simplifications.map mkCIdent
  }

private partial def mentionsRegisteredConstructor (stx : Syntax) :
    Lean.Elab.Term.TermElabM Bool := do
  if stx.isIdent then
    try
      let name ← Lean.resolveGlobalConstNoOverload stx
      if (getStructureConstructorInfo? (← Lean.getEnv) name).isSome then return true
    catch _ => pure ()
  for argument in stx.getArgs do
    if ← mentionsRegisteredConstructor argument then return true
  return false

private def prepareNativeSources (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) (imports : Array ImportedProgram) :
    Lean.Elab.Term.TermElabM (Array (TSyntax `sourceFunction) × Array NativeView) := do
  let mut headers : Array NativeHeader := #[]
  let mut needed := false
  for source in sources do
    let `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term
        $_termination:suffix) := source
      | Lean.throwErrorAt source "expected a named source function"
    let mut params : Array NativeParameter := #[]
    for parameter in parameters do
      let `(sourceParameter| ($param:ident : $type:term)) := parameter
        | Lean.throwErrorAt parameter "expected a named source parameter"
      let type ← elabPureType type
      needed := needed || !(← registeredTypeNames type.nativeType).isEmpty
      params := params.push { name := param, type := type }
    let result ← elabPureType result
    needed := needed || !(← registeredTypeNames result.nativeType).isEmpty
    needed := needed || (← mentionsRegisteredConstructor body.raw)
    headers := headers.push {
      name := name, params := params, result := result, native := generatedName family name ""
    }
  for source in imports do
    needed := needed || source.functions.any (·.nativeHeader.isSome)
  unless needed do return (sources, #[])
  let mut callees := headers
  for source in imports do
    for fn in source.functions do
      unless fn.pure do continue
      let name := mkIdentFrom source.name (source.name.getId ++ fn.name)
      let native := mkCIdent (source.family ++ fn.name)
      let header : NativeHeader ← match fn.nativeHeader with
        | some header => pure { header with name := name, native := native }
        | none => do
            let params ← fn.params.mapM fun (param, type) => do
              return ({
                name := mkIdentFrom source.name param
                type := ← resolvePureType (Lean.mkApp (Lean.mkConst ``Value) (coreTypeExpr type)) } :
                NativeParameter)
            pure ({
              name := name
              params := params
              native := native
              result := ← resolvePureType (Lean.mkApp (Lean.mkConst ``Value) (coreTypeExpr fn.result)) } :
              NativeHeader)
      callees := callees.push header
  let mut lowered := #[]
  let mut views := #[]
  for source in sources, header in headers do
    let `(sourceFunction| def $name:ident $_parameters:sourceParameter* : $_result:term := $body:term
        $termination:suffix) := source
      | Lean.throwErrorAt source "expected a named source function"
    let body ← lowerNativeBody callees header body
    let parameters ← header.params.mapM fun parameter => do
      let type ← Lean.Elab.liftMacroM (valueTypeTerm parameter.type.coreTy)
      `(sourceParameter| ($(parameter.name):ident : $type))
    let result ← Lean.Elab.liftMacroM (valueTypeTerm header.result.coreTy)
    lowered := lowered.push (← `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term
      $termination:suffix))
    views := views.push (← nativeView header)
  return (lowered, views)

private def elaborateProgram (family : TSyntax `ident)
    (functions : Array (TSyntax `sourceFunction)) (libraries : Array (TSyntax `ident))
    (pureMode : Bool := false) :
    Lean.Elab.Command.CommandElabM Unit := do
  let mut imports : Array ImportedProgram := #[]
  for library in libraries do
    let (name, functions) ← getProgramInfo library
    if imports.any (fun imported => imported.family == name) then
      Lean.throwErrorAt library "duplicate source program import"
    imports := imports.push ⟨library, name, functions⟩
  let (functions, nativeViews) ← if pureMode then
      Lean.Elab.Command.liftTermElabM (prepareNativeSources family functions imports)
    else pure (functions, #[])
  for source in functions do
    let fn ← Lean.Elab.liftMacroM (parseFunction source)
    let hints ← Lean.Elab.elabTerminationHints fn.termination
    if pureMode then
      if hints.partialFixpoint?.isSome then
        Lean.throwErrorAt fn.termination "pure source functions must terminate; partial fixed points are not supported"
    else if hints.isNotNone then
      Lean.throwErrorAt fn.termination "termination hints are checked by 'source_program (pure)'"
  let (declarations, information, coordinates) ←
    Lean.Elab.liftMacroM (programDeclarations family functions imports pureMode nativeViews)
  Lean.Elab.Command.elabCommand declarations
  registerProgramInfo family information
  registerLoopCoordinates coordinates

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
