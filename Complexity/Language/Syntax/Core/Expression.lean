/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Context
import Complexity.Language.Eval.Verification
import Complexity.Language.Eval.Node.Verification

/-!
# Typed source expressions and primitive actions

Internal expression checking and primitive construction for source atoms, calls, buffer and node
operations, assignments and returns. Operands here have already been normalized; the generated
code retains the existing typed operations and their actual source semantics.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def variableTerm (index : Nat) : MacroM (TSyntax `term) := do
  let mut result ← `(Complexity.Language.Var.here)
  for _ in [:index] do
    result ← `(Complexity.Language.Var.there $result)
  return result

def lookupBinding (scope : Scope) (name : TSyntax `ident) : MacroM (Binding × Nat) := do
  for (binding, index) in scope.zipIdx do
    if binding.name == some name.getId then
      return (binding, index)
  Macro.throwErrorAt name s!"unknown source variable '{name.getId}'"

private def lookupVariable (scope : Scope) (name : TSyntax `ident) : MacroM Atomic := do
  let (binding, index) ← lookupBinding scope name
  return ⟨binding.type, ← `(Complexity.Language.Atom.var $(← variableTerm index)),
    ← `($(binding.proofName):ident)⟩

partial def parseAtom (scope : Scope) (stx : TSyntax `term) : MacroM Atomic := do
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
def fieldAccess? (stx : TSyntax `term) : Option (TSyntax `term × Name) :=
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

partial def parsePrimitive (scope : Scope) (stx : TSyntax `term)
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

def checkAnnotation (annotation : Option (TSyntax `term)) (actual : Ty) : MacroM Unit := do
  if let some annotation := annotation then
    expectType annotation actual (← parseType annotation)

def bindingValueType (type : Ty) (annotation : Option (TSyntax `term))
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

def bindingNativeCoordinate (annotation : TSyntax `term) : Option NativeCoordinate :=
  match annotation with
  | `(source_native_type% ($_raw) ($native) via ($equiv)) => some ⟨native, equiv⟩
  | _ => none

private def lookupFunction (functions : Array Callee) (name : TSyntax `ident) : MacroM Callee := do
  let some fn := functions.find? (fun fn => fn.hasName name.getId)
    | Macro.throwErrorAt name s!"unknown source function '{name.getId}'; name a local function or a qualified imported function"
  return fn

def parseBinding (functions : Array Callee)
    (scope : Scope) (stx : TSyntax `term) :
    MacroM (Ty × TSyntax `term × TSyntax `term) := do
  let (head, operands) := match stx with
    | `($head:term $operands:term*) => (head, operands)
    | _ => (stx, #[])
  if head.raw.getId == `NodeRef.cons &&
      !functions.any (fun fn => fn.hasName head.raw.getId) then
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
    if field == `read && !functions.any (fun fn => fn.hasName head.raw.getId) then
      unless operands.isEmpty do
        Macro.throwErrorAt stx "a node read takes no arguments"
      let (kind, ref) ← parseNodeRef scope receiver
      return (.prod kind.toTy (.option (.node kind)),
        ← `(Complexity.Language.Stmt.readNode $(ref.term)),
        ← `(Complexity.Language.NodeRef.readM $(ref.value)))
  if let `($head:term $operands:term*) := stx then
    if head.raw.getId == `Buffer.alloc &&
        !functions.any (fun fn => fn.hasName head.raw.getId) then
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
          !functions.any (fun fn => fn.hasName head.raw.getId) then
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

def actionCode (functions : Array Callee)
    (scope : Scope) (action : TSyntax `term) : MacroM LoweredBlock := do
  if let `($head:term $_operands:term*) := action then
    if let some (_, field) := fieldAccess? head then
      if field == `set && !functions.any (fun fn => fn.hasName head.raw.getId) then
        return ← writeCode scope action
  let (resultType, statement, invocation) ← parseBinding functions scope action
  unless resultType == .unit do
    Macro.throwErrorAt action
      "a standalone source call must return Unit; bind its result with 'let name ← ...'"
  -- The callee's Unit result has only this empty lexical scope. The existing
  -- call boundary retains the actual final heap before the next statement.
  return ⟨← `($statement Complexity.Language.Stmt.skip),
    #[← `(doElem| $invocation:term)], true, #[]⟩

def assignCode (scope : Scope) (name : TSyntax `ident) (value : TSyntax `term) :
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

def assignBindingCode (functions : Array Callee)
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

def returnCode (scope : Scope) (result : Ty) (value : TSyntax `term) :
    MacroM LoweredBlock := do
  let parsed ← parsePrimitive scope value (some result)
  expectType value parsed.type result
  let term ← match parsed.atom with
    | some atom => `(Complexity.Language.Stmt.ret $atom)
    | none =>
        `(Complexity.Language.Stmt.letPrim $(parsed.term)
          (Complexity.Language.Stmt.ret (Complexity.Language.Atom.var Complexity.Language.Var.here)))
  return ⟨term, #[← `(doElem| return $(parsed.value))], false, #[]⟩

end Core

end Complexity.Language.Syntax
