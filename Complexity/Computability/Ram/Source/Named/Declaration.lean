/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Basic

/-!
# Source declarations in ordinary correctness proofs

`ram_def p := ram_functions% { ... }` declares callable functions without a
main statement. `ram_def p := ram_program% { ... }` additionally supplies a
main statement. Both preserve the quoted function table and export ordinary
Lean declarations for its functions and source names:

* `p.function.f` is the actual `Ram.Func` in the table;
* `p.functionIndex.f` is the function-table index of `f`;
* `p.function_lookup.f` proves that this entry is `p.function.f`;
* `p.body_eq.f` and `p.result_eq.f` expose the lowered body and return expression;
* `p.arguments.f` takes the declared parameters as words and constructs their argument list;
* `p.arguments_length.f` proves that this list has the function's declared arity;
* `p.localReg.f.x` is parameter or local `x` in function `f`;
* `p.mainReg.x` is local `x` in `main`, when a main statement is present.

Thus contracts can use `s.regs p.localReg.f.x` and `s.setReg p.mainReg.x value`
without reproducing register numbers. The register abbreviations use the
surface language's own `makeLocalScope` and `resolveLocal`, including the
parameter-before-local order. Function indices use declaration order, exactly
as named calls do. Function names, function locals and main locals remain in
separate namespaces; the usual Lean declaration-name collision errors apply.

Function abbreviations select the quoted table entry. Body and result equations
reuse terms from that same lowering, so proofs can unfold source definitions
without maintaining a second syntax tree. The command first invokes the term
macro, preserving its name-resolution errors and generated AST. No runtime lookup
is introduced, and the compiler and verification rules are unchanged. Existing
term-form declarations need not be migrated.
-/

namespace Ram.DSL

open Lean.Parser.Term

private def localRegisterDeclarations (scopeName : Lean.Name)
    (names : Array (Lean.TSyntax `ident)) : Lean.MacroM (Array Lean.Syntax) := do
  let scope ← makeLocalScope names
  names.mapM fun name => do
    let register ← resolveLocal scope Bool.true name
    let alias := Lean.mkIdentFrom name (scopeName ++ name.getId)
    let declaration ← `(command| abbrev $alias:ident : Ram.Reg := $register)
    return declaration.raw

private def argumentDeclarations (name fn : Lean.TSyntax `ident)
    (params : Array (Lean.TSyntax `ident)) (functionName : Lean.TSyntax `ident) :
    Lean.MacroM (Array Lean.Syntax) := do
  let argumentsName := Lean.mkIdentFrom fn (name.getId ++ `arguments ++ fn.getId)
  let lengthName := Lean.mkIdentFrom fn (name.getId ++ `arguments_length ++ fn.getId)
  let width := Lean.mkIdent (← Lean.Macro.addMacroScope `w)
  let mut value ← `(([$params:ident,*] : List (Ram.Word $width:ident)))
  for param in params.reverse do
    value ← `(fun ($param:ident : Ram.Word $width:ident) => $value)
  let arguments ← `(command| abbrev $argumentsName:ident {$width:ident : Nat} := $value)
  let mut application ← `(@$argumentsName:ident $width:ident)
  for param in params do
    application ← `($application $param:ident)
  let mut arity ← `(($application).length = ($functionName:ident).params)
  let mut proof ← `(Eq.refl ($application).length)
  for param in params.reverse do
    arity ← `(∀ ($param:ident : Ram.Word $width:ident), $arity)
    proof ← `(fun ($param:ident : Ram.Word $width:ident) => $proof)
  let length ← `(command| theorem $lengthName:ident {$width:ident : Nat} : $arity := $proof)
  return #[arguments.raw, length.raw]

private def loweredDeclarations (lowered : Lean.TSyntax `term) :
    Lean.MacroM (Array (Lean.TSyntax `term)) := do
  match lowered with
  | `(Ram.Named.Functions.mk $_registers:term [$declarations:term,*]) =>
      return declarations.getElems
  | `(Ram.Named.Bundle.mk $_registers:term [$declarations:term,*] $_main:term) =>
      return declarations.getElems
  | _ => Lean.Macro.throwErrorAt lowered "expected a lowered RAM declaration"

private def functionEquations (name fn functionName : Lean.TSyntax `ident)
    (lowered : Lean.TSyntax `term) : Lean.MacroM (Array Lean.Syntax) := do
  match lowered with
  | `(($_label:str, Ram.Func.mk $_params:term $_locals:term $body:term $result:term)) =>
      let bodyName := Lean.mkIdentFrom fn (name.getId ++ `body_eq ++ fn.getId)
      let bodyEquation ← `(command| theorem $bodyName:ident :
        ($functionName:ident).body = $body := rfl)
      let resultName := Lean.mkIdentFrom fn (name.getId ++ `result_eq ++ fn.getId)
      let resultEquation ← `(command| theorem $resultName:ident :
        ($functionName:ident).result = $result := rfl)
      return #[bodyEquation.raw, resultEquation.raw]
  | _ => Lean.Macro.throwErrorAt lowered "expected a lowered RAM function"

private def functionDeclarations (name : Lean.TSyntax `ident)
    (decls : Array (Lean.TSyntax `ramDecl)) (functions : Array (Lean.TSyntax `term)) :
    Lean.MacroM (Array Lean.Syntax) := do
  let mut declarations := #[]
  let mut index := 0
  for (decl, lowered) in decls.zip functions do
    match decl with
    | `(ramDecl| fn $fn:ident($params:ident,*) $_keyword:ident($locals:ident,*) {
        $_body:ramStmt* return $_result:ramExpr; }) =>
        let indexName := Lean.mkIdentFrom fn
          (name.getId ++ `functionIndex ++ fn.getId)
        let literal := Lean.Syntax.mkNumLit (toString index)
        let functionIndex ← `(command| abbrev $indexName:ident : Nat := $literal:num)
        declarations := declarations.push functionIndex.raw
        let functionName := Lean.mkIdentFrom fn (name.getId ++ `function ++ fn.getId)
        let function ← `(command| abbrev $functionName:ident : Ram.Func :=
          ($name:ident).program[$indexName:ident]'(by decide))
        declarations := declarations.push function.raw
        let lookupName := Lean.mkIdentFrom fn (name.getId ++ `function_lookup ++ fn.getId)
        let lookup ← `(command| theorem $lookupName:ident :
          ($name:ident).program[$indexName:ident]? = some $functionName:ident := by rfl)
        declarations := declarations.push lookup.raw
        declarations := declarations ++ (← functionEquations name fn functionName lowered)
        declarations := declarations ++ (← argumentDeclarations name fn params.getElems functionName)
        declarations := declarations ++ (← localRegisterDeclarations
          (name.getId ++ `localReg ++ fn.getId) (params.getElems ++ locals.getElems))
        index := index + 1
    | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"
  return declarations

/-- Declare named RAM functions or a named bundle, exporting their functions,
lookup theorems and source-level variable names for ordinary correctness proofs. -/
syntax (name := ramDef) (docComment)? "ram_def " ident " := " term : command

macro_rules
  | `(command| $[$doc:docComment]? ram_def $name:ident := $source:term) => do
      let (type, decls, mainNames) ← match source with
        | `(ram_functions% { $decls:ramDecl* }) =>
            pure (← `(Ram.Named.Functions), decls, #[])
        | `(ram_program% { $decls:ramDecl*
            main $_mainLocals:ident ($mainNames:ident,*) { $_mainBody:ramStmt* } }) =>
            pure (← `(Ram.Named.Bundle), decls, mainNames.getElems)
        | _ =>
            Lean.Macro.throwErrorAt source
              "ram_def expects ram_functions% { ... } or ram_program% { ... }"
      let some lowered ← Lean.expandMacro? source
        | Lean.Macro.throwErrorAt source "expected a RAM declaration quotation"
      let lowered : Lean.TSyntax `term := ⟨lowered⟩
      let declaration ← `(command| $[$doc:docComment]? def $name:ident : $type := $lowered)
      let functions ← loweredDeclarations lowered
      let mut declarations := #[declaration.raw] ++ (← functionDeclarations name decls functions)
      declarations := declarations ++ (← localRegisterDeclarations
        (name.getId ++ `mainReg) mainNames)
      return Lean.mkNullNode declarations

end Ram.DSL
