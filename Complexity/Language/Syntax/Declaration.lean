/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Lean.Elab.Command
import Lean.Elab.Term

/-!
# Shared source declarations

All source proof views parse the same explicitly typed declaration. Parsing
retains the original body and termination suffix; it neither chooses a model
nor lowers a control construct. Resolved types and checked source identities
are recorded separately in `Syntax.Imports`.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

/-- One explicitly typed source parameter. -/
declare_syntax_cat sourceParameter
syntax "(" ident " : " term ")" : sourceParameter

/-- A source function uses an ordinary parsed Lean body. -/
declare_syntax_cat sourceFunction
syntax "def " ident sourceParameter* " : " term " := " term
  Lean.Parser.Termination.suffix : sourceFunction

/-- A parameter before resolving its mathematical or source type. -/
structure ParsedParameter where
  name : TSyntax `ident
  type : TSyntax `term

/-- One source declaration, shared by lowering and optional proof views. -/
structure ParsedDeclaration where
  name : TSyntax `ident
  params : Array ParsedParameter
  result : TSyntax `term
  body : TSyntax `term
  termination : TSyntax ``Lean.Parser.Termination.suffix

/-- Parse one declaration and reject repeated parameter names before any view
is prepared. Its body and termination evidence remain unchanged. -/
def parseDeclaration (stx : TSyntax `sourceFunction) : MacroM ParsedDeclaration := do
  let `(sourceFunction| def $name:ident $parameters:sourceParameter* : $result:term := $body:term
      $termination:suffix) := stx
    | Macro.throwErrorAt stx "expected 'def name (argument : type) : type := do ...'"
  let mut params : Array ParsedParameter := #[]
  for parameter in parameters do
    let `(sourceParameter| ($param:ident : $type:term)) := parameter
      | Macro.throwErrorAt parameter "expected a source parameter '(name : type)'"
    if params.any (fun previous => previous.name.getId == param.getId) then
      Macro.throwErrorAt param "duplicate source parameter name"
    params := params.push ⟨param, type⟩
  return { name, params, result, body, termination }

/-- Rebuild the shared declaration after an explicit type/body preparation.
This only constructs syntax for the existing source emitter. -/
def ParsedDeclaration.toSyntax (declaration : ParsedDeclaration) :
    MacroM (TSyntax `sourceFunction) := do
  let parameters ← declaration.params.mapM fun parameter =>
    `(sourceParameter| ($(parameter.name):ident : $(parameter.type):term))
  `(sourceFunction| def $(declaration.name):ident $parameters:sourceParameter* :
    $(declaration.result):term := $(declaration.body):term
    $(declaration.termination):suffix)

end Complexity.Language.Syntax
