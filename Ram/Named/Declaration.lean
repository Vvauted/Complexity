/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Named

/-!
# Named registers in ordinary correctness proofs

`ram_def p := ram_program% { ... }` declares the same `Named.Bundle` as the
term form and exports ordinary reducible names for its static indices:

* `p.functionIndex.f` is the function-table index of `f`;
* `p.localReg.f.x` is parameter or local `x` in function `f`;
* `p.mainReg.x` is local `x` in `main`.

Thus contracts can use `s.regs p.localReg.f.x` and `s.setReg p.mainReg.x value`
without reproducing register numbers. The register abbreviations use the
surface language's own `makeLocalScope` and `resolveLocal`, including the
parameter-before-local order. Function indices use declaration order, exactly
as named calls do. Function names, function locals and main locals remain in
separate namespaces; the usual Lean declaration-name collision errors apply.

The command first invokes the existing `ram_program%` macro, preserving its
name-resolution errors and generated AST. No names are added to `Bundle`, no
runtime lookup is introduced, and the compiler and verification rules are
unchanged. Existing term-form declarations need not be migrated.
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

/-- Declare a named RAM bundle and export its source-level variable and
function names as ordinary Lean abbreviations for correctness proofs. -/
syntax (name := ramDef) (docComment)? "ram_def " ident " := " term : command

macro_rules
  | `(command| $[$doc:docComment]? ram_def $name:ident := $source:term) => do
      match source with
      | `(ram_program% { $decls:ramDecl*
          main $_mainLocals:ident ($mainNames:ident,*) { $_mainBody:ramStmt* } }) =>
          let some lowered ← Lean.expandMacro? source
            | Lean.Macro.throwErrorAt source "expected a RAM program quotation"
          let lowered : Lean.TSyntax `term := ⟨lowered⟩
          let declaration ← `(command| $[$doc:docComment]?
            def $name:ident : Ram.Named.Bundle := $lowered)
          let mut declarations := #[declaration.raw]
          let mut index := 0
          for decl in decls do
            match decl with
            | `(ramDecl| fn $fn:ident($params:ident,*) $_keyword:ident($locals:ident,*) {
                $_body:ramStmt* return $_result:ramExpr; }) =>
                let alias := Lean.mkIdentFrom fn
                  (name.getId ++ `functionIndex ++ fn.getId)
                let literal := Lean.Syntax.mkNumLit (toString index)
                let functionIndex ← `(command| abbrev $alias:ident : Nat := $literal:num)
                declarations := declarations.push functionIndex.raw
                declarations := declarations ++ (← localRegisterDeclarations
                  (name.getId ++ `localReg ++ fn.getId) (params.getElems ++ locals.getElems))
                index := index + 1
            | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"
          declarations := declarations ++ (← localRegisterDeclarations
            (name.getId ++ `mainReg) mainNames.getElems)
          return Lean.mkNullNode declarations
      | _ => Lean.Macro.throwErrorAt source "ram_def expects ram_program% { ... }"

end Ram.DSL
