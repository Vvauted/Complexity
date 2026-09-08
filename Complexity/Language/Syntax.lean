/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Basic
import Lean.Elab.Command
import Lean.Parser.Do

/-!
# Named scalar source programs

`source_program P where` declares an independent typed source program from
Lean-style function headers and `do` blocks. The scalar subset supports
`Nat`, `Bool`, `Unit`, immutable lexical `let`, named first-order calls,
`if`/`then`/`else` and `return`. Addition and comparisons accept atomic
operands; a compound return or condition introduces an actual core primitive
binding. More deeply nested expressions must first be named with `let`.

The declaration exports `P.signatures`, `P.fId`, `P.fBody` and `P.program`,
together with the ordinary curried observation `P.f`. This noncomputable
`Part (Except Fault result)` observes the actual independent source execution;
it is a mathematical proof interface, not a host executable for `#eval`.
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

/-- A scalar source function uses an ordinary parsed Lean `do` body. -/
declare_syntax_cat sourceFunction
syntax "def " ident sourceParameter* " : " term " := " term : sourceFunction

/-- Declare a finite family of named, independently interpreted scalar functions. -/
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

private abbrev Scope := List (Option Name × Ty)

private structure Atomic where
  type : Ty
  term : TSyntax `term

private structure Primitive where
  type : Ty
  term : TSyntax `term
  atom : Option (TSyntax `term)

-- These witnesses justify the partial elaborator definitions; no translation
-- branch uses them as a default source expression.
private instance : Nonempty Atomic :=
  ⟨⟨.unit, ⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩⟩⟩

private instance : Nonempty Primitive :=
  ⟨⟨.unit, Lean.Syntax.mkCApp ``Complexity.Language.Prim.atom
      #[⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩],
    some ⟨(mkCIdent ``Complexity.Language.Atom.unit).raw⟩⟩⟩

private def typeName : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"

private def parseType (stx : TSyntax `term) : MacroM Ty := do
  match stx with
  | `(Nat) => return .nat
  | `(Bool) => return .bool
  | `(Unit) => return .unit
  | _ => Macro.throwErrorAt stx "supported source types are Nat, Bool and Unit"

private def typeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Complexity.Language.Ty.nat)
  | .bool => `(Complexity.Language.Ty.bool)
  | .unit => `(Complexity.Language.Ty.unit)

private def valueTypeTerm : Ty → MacroM (TSyntax `term)
  | .nat => `(Nat)
  | .bool => `(Bool)
  | .unit => `(Unit)

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

private def lookupVariable (scope : Scope) (name : TSyntax `ident) : MacroM Atomic := do
  for ((binding, type), index) in scope.zipIdx do
    if binding == some name.getId then
      return ⟨type, ← `(Complexity.Language.Atom.var $(← variableTerm index))⟩
  Macro.throwErrorAt name s!"unknown source variable '{name.getId}'"

private partial def parseAtom (scope : Scope) (stx : TSyntax `term) : MacroM Atomic := do
  match stx with
  | `(($value:term)) => parseAtom scope value
  | `(true) => return ⟨.bool, ← `(Complexity.Language.Atom.bool true)⟩
  | `(false) => return ⟨.bool, ← `(Complexity.Language.Atom.bool false)⟩
  | `(()) => return ⟨.unit, ← `(Complexity.Language.Atom.unit)⟩
  | `($value:num) => return ⟨.nat, ← `(Complexity.Language.Atom.nat $value:num)⟩
  | `($name:ident) => lookupVariable scope name
  | _ =>
      Macro.throwErrorAt stx
        "expected a source variable or scalar literal; name a compound operand with 'let' first"

private def binaryPrimitive (scope : Scope) (left right : TSyntax `term)
    (result : Ty) (constructor : Name) : MacroM Primitive := do
  let lhs ← parseAtom scope left
  let rhs ← parseAtom scope right
  expectType left lhs.type .nat
  expectType right rhs.type .nat
  let op := mkCIdent constructor
  return ⟨result, ← `($op $(lhs.term) $(rhs.term)), none⟩

private partial def parsePrimitive (scope : Scope) (stx : TSyntax `term) : MacroM Primitive := do
  match stx with
  | `(($value:term)) => parsePrimitive scope value
  | `($left + $right) => binaryPrimitive scope left right .nat ``Prim.add
  | `($left < $right) => binaryPrimitive scope left right .bool ``Prim.lt
  | `($left ≤ $right) => binaryPrimitive scope left right .bool ``Prim.le
  | `($left <= $right) => binaryPrimitive scope left right .bool ``Prim.le
  | _ =>
      let atom ← parseAtom scope stx
      return ⟨atom.type, ← `(Complexity.Language.Prim.atom $(atom.term)), some atom.term⟩

private def checkAnnotation (annotation : Option (TSyntax `term)) (actual : Ty) : MacroM Unit := do
  if let some annotation := annotation then
    expectType annotation actual (← parseType annotation)

private def lookupFunction (functions : Array Function) (name : TSyntax `ident) : MacroM Function := do
  let some fn := functions.find? (fun fn => fn.name.getId == name.getId)
    | Macro.throwErrorAt name s!"unknown source function '{name.getId}'; calls must name this program's functions"
  return fn

private def parseCall (functions : Array Function) (scope : Scope) (stx : TSyntax `term) :
    MacroM (Function × TSyntax `term) := do
  let (name, operands) ← match stx with
    | `($name:ident $operands:term*) => pure (name, operands)
    | `($name:ident) => pure (name, #[])
    | _ => Macro.throwErrorAt stx "expected a named source call 'function argument ...'"
  let fn ← lookupFunction functions name
  unless operands.size == fn.params.size do
    Macro.throwErrorAt stx s!"source function '{name.getId}' expects {fn.params.size} arguments, found {operands.size}"
  let mut atoms : Array (TSyntax `term) := #[]
  for operand in operands, param in fn.params do
    let atom ← parseAtom scope operand
    expectType operand atom.type param.type
    atoms := atoms.push atom.term
  let mut args ← `(Complexity.Language.Args.nil)
  for atom in atoms.reverse do
    args ← `(Complexity.Language.Args.cons $atom $args)
  return (fn, args)

private def returnCode (scope : Scope) (result : Ty) (value : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let parsed ← parsePrimitive scope value
  expectType value parsed.type result
  match parsed.atom with
  | some atom => `(Complexity.Language.Stmt.ret $atom)
  | none =>
      `(Complexity.Language.Stmt.letPrim $(parsed.term)
        (Complexity.Language.Stmt.ret (Complexity.Language.Atom.var Complexity.Language.Var.here)))

private partial def blockCode (family : TSyntax `ident) (functions : Array Function)
    (scope : Scope) (result : Ty) (elements : List (TSyntax `doElem)) :
    MacroM (TSyntax `term) := do
  match elements with
  | [] => `(Complexity.Language.Stmt.skip)
  | element :: rest => withRef element do
      match element with
      | `(doElem| let $name:ident $[: $annotation:term]? := $value:term) =>
          let parsed ← parsePrimitive scope value
          checkAnnotation annotation parsed.type
          let body ← blockCode family functions ((some name.getId, parsed.type) :: scope) result rest
          `(Complexity.Language.Stmt.letPrim $(parsed.term) $body)
      | `(doElem| let $name:ident $[: $annotation:term]? ← $action:term) =>
          let (fn, args) ← parseCall functions scope action
          checkAnnotation annotation fn.result
          let body ← blockCode family functions ((some name.getId, fn.result) :: scope) result rest
          let id := generatedName family fn.name "Id"
          `(Complexity.Language.Stmt.call $id:ident $args $body)
      | _ =>
          let statement ← match element with
            | `(doElem| return $value:term) => returnCode scope result value
            | `(doElem| return) => returnCode scope result (← `(()))
            | `(doElem| if $condition:term then $yes:doSeq else $no:doSeq) => do
                let parsed ← parsePrimitive scope condition
                expectType condition parsed.type .bool
                match parsed.atom with
                | some atom =>
                    let yesCode ← blockCode family functions scope result (getDoElems yes).toList
                    let noCode ← blockCode family functions scope result (getDoElems no).toList
                    `(Complexity.Language.Stmt.ite $atom $yesCode $noCode)
                | none =>
                    let inner := (none, Ty.bool) :: scope
                    let yesCode ← blockCode family functions inner result (getDoElems yes).toList
                    let noCode ← blockCode family functions inner result (getDoElems no).toList
                    `(Complexity.Language.Stmt.letPrim $(parsed.term)
                      (Complexity.Language.Stmt.ite
                        (Complexity.Language.Atom.var Complexity.Language.Var.here) $yesCode $noCode))
            | _ =>
                Macro.throwErrorAt element
                  "unsupported source statement; use immutable let, a named call, if/then/else, or return"
          if rest.isEmpty then
            return statement
          else
            let continuation ← blockCode family functions scope result rest
            `(Complexity.Language.Stmt.seq $statement $continuation)

private def functionCode (family : TSyntax `ident) (functions : Array Function)
    (fn : Function) : MacroM (TSyntax `term) := do
  match fn.body with
  | `(do $body:doSeq) =>
      let scope := fn.params.toList.map fun param => (some param.name.getId, param.type)
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
  let mut type ← `(Part (Except Complexity.Language.Fault $result))
  let mut value ← `(Complexity.Language.Program.eval $programName:ident $id:ident $arguments)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    value ← `(fun ($parameter:ident : $parameterType) => $value)
  let declaration ← `(command|
    /-- The named function's actual partial source result, with ordinary typed arguments. -/
    noncomputable def $name:ident : $type := $value)
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
  for fn in functions do
    let name := generatedName family fn.name "Body"
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    let body ← functionCode family functions fn
    let declaration ← `(command|
      /-- The named function's actual independently interpreted source body. -/
      def $name:ident : Complexity.Language.Stmt $signaturesName:ident $params $result := $body)
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
  return mkNullNode declarations

elab_rules : command
  | `(command| source_program $family:ident where $functions:sourceFunction*) => do
      let declarations ← Lean.Elab.liftMacroM (programDeclarations family functions)
      Lean.Elab.Command.elabCommand declarations

end Complexity.Language.Syntax
