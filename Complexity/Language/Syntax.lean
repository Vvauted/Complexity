/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Continuation
import Complexity.Language.Eval.Verification
import Lean.Elab.Command
import Lean.Elab.Do
import Lean.Parser.Do

/-!
# Named source programs with borrowed buffers

`source_program P where` declares an independent typed source program from
Lean-style function headers and `do` blocks. The supported types are
`Nat`, `Bool`, `Unit`, `Buffer Nat` and `Buffer Bool`, with lexical `let` and
`let mut`, assignment, named first-order calls, `if`/`then`/`else` and `return`.
Only the nearest mutable binding may be assigned; ordinary `let` bindings and
parameters are immutable. `x ← action` rebinds a mutable local to the actual
result of a supported named call, buffer read or slice. Natural arithmetic and
comparisons may be nested in bindings, assignments, return values, conditions
and call arguments. Their operands are normalized left to right into actual
lexical primitive bindings; no host
computation replaces the generated operations.

Borrowed buffers expose `xs.length`, `let x ← xs.get i`, `xs.set i value` and
`let ys ← xs.slice offset length`. Reads and writes observe the current shared
heap; copying, passing or returning a buffer does not copy its contents. Buffer
parameters and results use the existing `Buffer .nat`/`Buffer .bool` Lean types.
There are no buffer literals, object-identifier constructors or host callbacks.

The declaration exports `P.signatures`, `P.fId`, `P.fBody` and `P.program`,
together with the ordinary curried observation `P.f` and its equation `P.f_eq`.
The equation exposes one body using ordinary `ExceptT Fault (StateT Heap Part)` notation,
keeping named callee observations opaque. It is not a global simp rule.
`P.f_total_iff` connects arbitrary ordinary curried preconditions and
postconditions, including initial and final heaps, to the source contract without
manual environment decomposition. The noncomputable action takes the actual
initial heap and observes `Part (Except Fault result × Heap)`; no empty heap is
supplied implicitly. It is a mathematical proof interface, not a host executable
for `#eval`.
All signatures are collected before any body is translated, so forward calls
and mutual recursion refer to actual entries of the same program. This does
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
syntax "def " ident sourceParameter* " : " term " := " term : sourceFunction

/-- Declare a finite family of named, independently interpreted source functions. -/
syntax (name := sourceProgram) "source_program " ident " where" ppLine
  many1Indent(sourceFunction) : command

private structure Parameter where
  name : TSyntax `ident
  type : Ty

private structure Function where
  name : TSyntax `ident
  params : Array Parameter
  result : Ty
  body : TSyntax `term

private structure Binding where
  name : Option Name
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

private structure LoweredBlock where
  term : TSyntax `term
  proofBody : Array (TSyntax `doElem)
  fallsThrough : Bool

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
  ⟨⟨⟨(mkCIdent ``Complexity.Language.Stmt.skip).raw⟩, #[], true⟩⟩

private instance : Nonempty NormalizedValue :=
  ⟨⟨#[], ⟨(mkCIdent ``Unit.unit).raw⟩, true⟩⟩

private def typeName : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .buffer .nat => "Buffer Nat"
  | .buffer .bool => "Buffer Bool"

private def parseType (stx : TSyntax `term) : MacroM Ty := do
  match stx with
  | `(Nat) => return .nat
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | `(Buffer Nat) => return .buffer .nat
  | `(Buffer Bool) => return .buffer .bool
  | _ => Macro.throwErrorAt stx "supported source types are Nat, Bool, Unit, Buffer Nat and Buffer Bool"

private def typeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Complexity.Language.Ty.nat)
  | .bool => `(Complexity.Language.Ty.bool)
  | .unit => `(Complexity.Language.Ty.unit)
  | .buffer .nat => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Ty.buffer Complexity.Language.CellTy.bool)

private def valueTypeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)
  | .buffer .nat => `(Complexity.Language.Buffer Complexity.Language.CellTy.nat)
  | .buffer .bool => `(Complexity.Language.Buffer Complexity.Language.CellTy.bool)

private def expectType (stx : Syntax) (actual expected : Ty) : MacroM Unit := do
  unless actual == expected do
    Macro.throwErrorAt stx s!"expected source type {typeName expected}, found {typeName actual}"

private def parameterTypes (params : Array Parameter) : MacroM (TSyntax `term) := do
  let types ← params.mapM fun param => typeTerm param.type
  `([$types,*])

private def generatedName (family : TSyntax `ident) (fn : TSyntax `ident)
    (suffix : String) : TSyntax `ident :=
  mkIdentFrom fn (family.getId ++ Name.mkSimple (fn.getId.toString ++ suffix))

private def parseFunction (stx : TSyntax `sourceFunction) : MacroM Function := do
  match stx with
  | `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term) =>
      let mut params : Array Parameter := #[]
      for parameter in parameters do
        match parameter with
        | `(sourceParameter| ($param:ident : $type:term)) =>
            if params.any (fun previous => previous.name.getId == param.getId) then
              Macro.throwErrorAt param "duplicate source parameter name"
            params := params.push ⟨param, ← parseType type⟩
        | _ => Macro.throwErrorAt parameter "expected a source parameter '(name : type)'"
      return ⟨name, params, ← parseType result, body⟩
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
    ← `($name:ident)⟩

private partial def parseAtom (scope : Scope) (stx : TSyntax `term) : MacroM Atomic := do
  match stx with
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

private partial def parsePrimitive (scope : Scope) (stx : TSyntax `term) : MacroM Primitive := do
  if let some (receiver, field) := fieldAccess? stx then
    if field == `length then
      let (_, buffer) ← parseBuffer scope receiver
      return ⟨.nat, ← `(Complexity.Language.Prim.length $(buffer.term)), none,
        ← `(Complexity.Language.Buffer.length $(buffer.value))⟩
  match stx with
  | `(($value:term)) => parsePrimitive scope value
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

private def lookupFunction (functions : Array Function) (name : TSyntax `ident) : MacroM Function := do
  let some fn := functions.find? (fun fn => fn.name.getId == name.getId)
    | Macro.throwErrorAt name s!"unknown source function '{name.getId}'; calls must name this program's functions"
  return fn

private def parseBinding (family : TSyntax `ident) (functions : Array Function)
    (scope : Scope) (stx : TSyntax `term) :
    MacroM (Ty × TSyntax `term × TSyntax `term) := do
  if let `($head:term $operands:term*) := stx then
    if let some (receiver, field) := fieldAccess? head then
      if field == `get || field == `slice then
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
  let name := generatedName family fn.name ""
  let id := generatedName family fn.name "Id"
  return (fn.result, ← `(Complexity.Language.Stmt.call $id:ident $args),
    Lean.Syntax.mkApp ⟨name.raw⟩ values)

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
    true⟩

private def assignCode (scope : Scope) (name : TSyntax `ident) (value : TSyntax `term) :
    MacroM LoweredBlock := do
  -- The normalizer has already introduced every RHS temporary into this scope.
  -- Looking up the target here therefore uses its actual, possibly lifted index.
  let (binding, index) ← lookupBinding scope name
  unless binding.isMutable do
    Macro.throwErrorAt name s!"source variable '{name.getId}' is immutable; declare it with 'let mut'"
  let parsed ← parsePrimitive scope value
  expectType value parsed.type binding.type
  return ⟨← `(Complexity.Language.Stmt.assign $(← variableTerm index) $(parsed.term)),
    #[← `(doElem| $name:ident := $(parsed.value))], true⟩

private def assignBindingCode (family : TSyntax `ident) (functions : Array Function)
    (scope : Scope) (name : TSyntax `ident) (action : TSyntax `term) : MacroM LoweredBlock := do
  let (binding, index) ← lookupBinding scope name
  unless binding.isMutable do
    Macro.throwErrorAt name s!"source variable '{name.getId}' is immutable; declare it with 'let mut'"
  let (resultType, statement, invocation) ← parseBinding family functions scope action
  expectType action resultType binding.type
  -- The action's fresh result is innermost only for this assignment. Leaving
  -- that scope drops the result slot, retaining the updated outer binding.
  let assignment ← `(Complexity.Language.Stmt.assign
    (Complexity.Language.Var.there $(← variableTerm index))
    (Complexity.Language.Prim.atom (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨← `($statement $assignment), #[← `(doElem| $name:ident ← $invocation:term)], true⟩

private def returnCode (scope : Scope) (result : Ty) (value : TSyntax `term) :
    MacroM LoweredBlock := do
  let parsed ← parsePrimitive scope value
  expectType value parsed.type result
  let term ← match parsed.atom with
    | some atom => `(Complexity.Language.Stmt.ret $atom)
    | none =>
        `(Complexity.Language.Stmt.letPrim $(parsed.term)
          (Complexity.Language.Stmt.ret (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨term, #[← `(doElem| return $(parsed.value))], false⟩

private def doSequence (elements : Array (TSyntax `doElem)) : TSyntax ``doSeq :=
  ⟨Lean.Elab.Term.Do.mkDoSeq (elements.map (·.raw))⟩

private def LoweredBlock.proofSequence (block : LoweredBlock) (normal : TSyntax `doElem) :
    TSyntax ``doSeq :=
  doSequence (if block.fallsThrough then block.proofBody.push normal else block.proofBody)

-- Normalize only the supported expression vocabulary. Fresh lexical names are
-- consumed by the ordinary typed translator and cannot capture user bindings.
private partial def normalizeValue (stx : TSyntax `term) (atomize : Bool) :
    MacroM NormalizedValue := withRef stx do
  let binary (left right : TSyntax `term)
      (rebuild : TSyntax `term → TSyntax `term → MacroM (TSyntax `term)) := do
    let lhs ← normalizeValue left true
    let rhs ← normalizeValue right true
    return (⟨lhs.bindings ++ rhs.bindings, ← rebuild lhs.value rhs.value, false⟩ : NormalizedValue)
  let normalized ← (match stx with
    | `(($value:term)) => normalizeValue value false
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
    | _ => pure ⟨#[], stx, !(fieldAccess? stx).any (fun access => access.2 == `length)⟩)
  if atomize && !normalized.atomic then
    let name := mkIdentFrom stx (← Macro.addMacroScope `operand)
    let binding ← `(doElem| let $name:ident := $(normalized.value))
    return ⟨normalized.bindings.push binding, ⟨name.raw⟩, true⟩
  else
    return normalized

private def normalizeCall (stx : TSyntax `term) :
    MacroM (Array (TSyntax `doElem) × TSyntax `term) := withRef stx do
  match stx with
  | `($head:term $operands:term*) =>
      let mut bindings := #[]
      let mut arguments := #[]
      for operand in operands do
        let normalized ← normalizeValue operand true
        bindings := bindings ++ normalized.bindings
        arguments := arguments.push normalized.value
      return (bindings, Lean.Syntax.mkApp head arguments)
  | _ => return (#[], stx)

private def normalizeElement (element : TSyntax `doElem) :
    MacroM (Array (TSyntax `doElem) × TSyntax `doElem) := withRef element do
  match element with
  | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeValue value false
      return (normalized.bindings,
        ← `(doElem| let mut $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
      let normalized ← normalizeValue value false
      return (normalized.bindings,
        ← `(doElem| let $name:ident $[: $annotation:term]? := $(normalized.value)))
  | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall action
      return (bindings, ← `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
      let (bindings, action) ← normalizeCall action
      return (bindings, ← `(doElem| let $name:ident $[: $annotation:term]? ← $action:term))
  | `(doElem| $name:ident := $value:term) =>
      let normalized ← normalizeValue value false
      return (normalized.bindings, ← `(doElem| $name:ident := $(normalized.value)))
  | `(doElem| $name:ident ← $action:term) =>
      let (bindings, action) ← normalizeCall action
      return (bindings, ← `(doElem| $name:ident ← $action:term))
  | `(doElem| return $value:term) =>
      let normalized ← normalizeValue value false
      return (normalized.bindings, ← `(doElem| return $(normalized.value)))
  | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) =>
      let normalized ← normalizeValue condition false
      return (normalized.bindings,
        ← `(doElem| if $(normalized.value) then $yes:doSeq else $no:doSeq))
  | `(doElem| $action:term) =>
      let (bindings, action) ← normalizeCall action
      return (bindings, ← `(doElem| $action:term))
  | _ => return (#[], element)

private partial def blockCode (family : TSyntax `ident) (functions : Array Function)
    (scope : Scope) (result : Ty) (elements : List (TSyntax `doElem)) :
    MacroM LoweredBlock := do
  match elements with
  | [] => return ⟨← `(Complexity.Language.Stmt.skip), #[], true⟩
  | element :: rest => withRef element do
      let (bindings, element) ← normalizeElement element
      if !bindings.isEmpty then
        return ← blockCode family functions scope result (bindings.toList ++ element :: rest)
      match element with
      | `(doElem| let mut $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value
          checkAnnotation annotation parsed.type
          let body ← blockCode family functions
            (⟨some name.getId, parsed.type, true⟩ :: scope) result rest
          let type ← valueTypeTerm parsed.type
          let binding ← `(doElem| let mut $name:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough⟩
      | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value
          checkAnnotation annotation parsed.type
          let body ← blockCode family functions
            (⟨some name.getId, parsed.type, false⟩ :: scope) result rest
          let type ← valueTypeTerm parsed.type
          let binding ← `(doElem| let $name:ident : $type := $(parsed.value))
          return ⟨← `(Complexity.Language.Stmt.letPrim $(parsed.term) $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough⟩
      | `(doElem| let mut $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding family functions scope action
          checkAnnotation annotation bindingType
          let body ← blockCode family functions
            (⟨some name.getId, bindingType, true⟩ :: scope) result rest
          let type ← valueTypeTerm bindingType
          let binding ← `(doElem| let mut $name:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough⟩
      | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
          let (bindingType, statement, invocation) ← parseBinding family functions scope action
          checkAnnotation annotation bindingType
          let body ← blockCode family functions
            (⟨some name.getId, bindingType, false⟩ :: scope) result rest
          let type ← valueTypeTerm bindingType
          let binding ← `(doElem| let $name:ident : $type ← $invocation:term)
          return ⟨← `($statement $(body.term)),
            #[binding] ++ body.proofBody, body.fallsThrough⟩
      | _ =>
          -- A term-valued match keeps its local `return` from exiting this block's translation.
          let statement ← (match element with
            | `(doElem| $name:ident := $value:term) => assignCode scope name value
            | `(doElem| $name:ident ← $action:term) =>
                assignBindingCode family functions scope name action
            | `(doElem| return $value:term) => returnCode scope result value
            | `(doElem| return) => do returnCode scope result (← `(()))
            | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) => do
                let parsed ← parsePrimitive scope condition
                expectType condition parsed.type .bool
                let inner := if parsed.atom.isSome then scope else ⟨none, Ty.bool, false⟩ :: scope
                let yesCode ← blockCode family functions inner result (getDoElems yes).toList
                let noCode ← blockCode family functions inner result (getDoElems no).toList
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
                let branch ← `(doElem|
                  if $(parsed.value) then $yesBody:doSeq else $noBody:doSeq)
                return ⟨term, #[branch], yesCode.fallsThrough || noCode.fallsThrough⟩
            | `(doElem| $action:term) => writeCode scope action
            | _ =>
                Macro.throwErrorAt element
                  "unsupported source statement; use let, let mut, assignment, a named call, buffer access, if/then/else, or return")
          if rest.isEmpty then
            return statement
          else
            let continuation ← blockCode family functions scope result rest
            return ⟨← `(Complexity.Language.Stmt.seq $(statement.term) $(continuation.term)),
              if statement.fallsThrough then statement.proofBody ++ continuation.proofBody
                else statement.proofBody,
              statement.fallsThrough && continuation.fallsThrough⟩

private def functionCode (family : TSyntax `ident) (functions : Array Function)
    (fn : Function) : MacroM LoweredBlock := do
  match fn.body with
  | `(do $body:doSeq) =>
      let scope : Scope := fn.params.toList.map fun param => ⟨some param.name.getId, param.type, false⟩
      blockCode family functions scope fn.result (getDoElems body).toList
  | _ => Macro.throwErrorAt fn.body "source function bodies must be supported 'do' blocks"

private def observationDeclaration (family programName : TSyntax `ident)
    (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name ""
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

private def equationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (lowered : LoweredBlock) : MacroM Syntax := do
  let name := generatedName family fn.name "_eq"
  let observation := generatedName family fn.name ""
  let bodyName := generatedName family fn.name "Body"
  let id := generatedName family fn.name "Id"
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let lhs := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let fallthrough ← `(doElem| throw Complexity.Language.Fault.missingReturn)
  let body := lowered.proofSequence fallthrough
  let result ← valueTypeTerm fn.result
  let mut type ← `($lhs = ((do $body:doSeq) : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof ← `(by
    have body_selected : ($programName:ident).body $id:ident = $bodyName:ident := rfl
    conv =>
      lhs
      unfold $observation:ident
      rw [Complexity.Language.Program.eval_eq_evalWith, body_selected]
    simp only [$bodyName:ident,
      Complexity.Language.Stmt.evalWith_skip, Complexity.Language.Stmt.evalWith_ret,
      Complexity.Language.Stmt.evalWith_assign,
      Complexity.Language.Stmt.evalWith_letPrim, Complexity.Language.Stmt.evalWith_seq,
      Complexity.Language.Stmt.evalWith_ite, Complexity.Language.Stmt.evalWith_call,
      Complexity.Language.Stmt.evalWith_read, Complexity.Language.Stmt.evalWith_write,
      Complexity.Language.Stmt.evalWith_slice,
      Complexity.Language.Atom.eval, Complexity.Language.Prim.eval, Complexity.Language.Args.eval,
      Complexity.Language.CellTy.toValue, Complexity.Language.CellTy.ofValue,
      Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there,
      Complexity.Language.Env.head_cons, Complexity.Language.Env.tail_cons,
      Complexity.Language.Env.get_tail, Complexity.Language.Env.set_here,
      Complexity.Language.Env.set_there, Complexity.Language.Env.tail_set_here,
      Complexity.Language.Env.tail_set_there, pure_bind]
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

private def totalDeclaration (family programName : TSyntax `ident)
    (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_total_iff"
  let observation := generatedName family fn.name ""
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
  let sourcePre := Lean.Syntax.mkApp ⟨pre.raw⟩ (envArguments.push ⟨initialHeap.raw⟩)
  let sourcePost := Lean.Syntax.mkApp ⟨post.raw⟩
    (envArguments ++ #[⟨initialHeap.raw⟩, ⟨value.raw⟩, ⟨finalHeap.raw⟩])
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
  let declaration ← `(command|
    /-- The source contract is equivalent to ordinary curried preconditions and
    successful result/heap postconditions, including termination and absence of faults. -/
    theorem $name:ident ($pre:ident : $preType) ($post:ident : $postType) :
        Complexity.Language.FunctionTotal $programName:ident $id:ident
          (fun $env:ident $initialHeap:ident => $sourcePre)
          (fun $env:ident $initialHeap:ident $value:ident $finalHeap:ident => $sourcePost) ↔
          $ordinary := by
      rw [Complexity.Language.FunctionTotal.iff_eval]
      exact ⟨$forward, $backward⟩)
  return declaration.raw

private def programDeclarations (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) : MacroM Syntax := do
  let mut functions : Array Function := #[]
  for source in sources do
    let fn ← parseFunction source
    if functions.any (fun previous => previous.name.getId == fn.name.getId) then
      Macro.throwErrorAt fn.name "duplicate source function name"
    functions := functions.push fn
  let signaturesName := mkIdentFrom family (family.getId ++ `signatures)
  let signatures ← functions.mapM fun fn => do
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    `(({ params := $params, result := $result } : Complexity.Language.Signature))
  let signatureDeclaration ← `(command|
    /-- The source program's declared first-order signatures. -/
    abbrev $signaturesName:ident : List Complexity.Language.Signature := [$signatures,*])
  let mut declarations := #[signatureDeclaration.raw]
  for (fn, index) in functions.zipIdx do
    let id := generatedName family fn.name "Id"
    let number := Syntax.mkNumLit (toString index)
    let declaration ← `(command|
      /-- This named source function's index in its declared signature table. -/
      abbrev $id:ident : Fin ($signaturesName:ident).length := ⟨$number:num, by decide⟩)
    declarations := declarations.push declaration.raw
  let mut loweredBodies : Array LoweredBlock := #[]
  for fn in functions do
    let name := generatedName family fn.name "Body"
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    let body ← functionCode family functions fn
    loweredBodies := loweredBodies.push body
    let declaration ← `(command|
      /-- The named function's actual independently interpreted source body. -/
      def $name:ident : Complexity.Language.Stmt $signaturesName:ident $params $result := $(body.term))
    declarations := declarations.push declaration.raw
  let mut bodies ← `(fun index => Fin.elim0 index)
  for fn in functions.reverse do
    let name := generatedName family fn.name "Body"
    bodies ← `(Fin.cases $name:ident $bodies)
  let programName := mkIdentFrom family (family.getId ++ `program)
  let programDeclaration ← `(command|
    /-- The finite table of actual named source bodies. -/
    def $programName:ident : Complexity.Language.Program $signaturesName:ident := { body := $bodies })
  declarations := declarations.push programDeclaration.raw
  for fn in functions do
    declarations := declarations.push (← observationDeclaration family programName fn)
  for fn in functions, body in loweredBodies do
    declarations := declarations.push (← equationDeclaration family programName fn body)
  for fn in functions do
    declarations := declarations.push (← totalDeclaration family programName fn)
  return mkNullNode declarations

elab_rules : command
  | `(command| source_program $family:ident where $functions:sourceFunction*) => do
      let declarations ← Lean.Elab.liftMacroM (programDeclarations family functions)
      Lean.Elab.Command.elabCommand declarations

end Complexity.Language.Syntax
