/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Basic
import Complexity.Computability.Ram.Source.Syntax

/-!
# Named functions and programs over the existing RAM language

`ram_functions%` declares functions without an entry point or input/output
wrapper. `ram_program%` additionally declares a main statement. Both collect
all function names before lowering any body, so calls can refer forward,
recurse, or participate in mutual recursion.
Functions and local variables have separate name tables. Embedded `const(t)`
terms retain the enclosing Lean scope and never refer to runtime registers.

The functions lower to the ordinary `Program`, with names kept as metadata.
`Ram.Named.Functions.withMain` explicitly supplies an entry point when one is
needed. `Ram.Named.Bundle.compile` is the existing checked compiler: arity and
register validity are not redefined here. Duplicate/unknown function names
and undeclared variables are reported while resolving the surface syntax.
-/

namespace Ram.Named

abbrev Declaration := String × Func

/-- Named function declarations without a distinguished entry point.
The register bound covers the functions' local frames. -/
structure Functions where
  registers : Nat
  declarations : List Declaration
  deriving DecidableEq, Repr

/-- The function table used by the existing execution and compilation rules. -/
def Functions.program (functions : Functions) : Program :=
  functions.declarations.map Prod.snd

/-- Function names remain paired with their bodies for readable inspection.
They are not runtime strings or a new instruction-level lookup operation. -/
structure Bundle where
  registers : Nat
  declarations : List Declaration
  main : Stmt
  deriving DecidableEq, Repr

def Bundle.program (bundle : Bundle) : Program := bundle.declarations.map Prod.snd

/-- Supply an explicit entry statement, leaving all function definitions
unchanged. The entry point need not perform any input or output. -/
def Functions.withMain (functions : Functions) (registers : Nat) (main : Stmt) : Bundle where
  registers := max registers functions.registers
  declarations := functions.declarations
  main := main

@[simp]
theorem Functions.withMain_program (functions : Functions) (registers : Nat) (main : Stmt) :
    (functions.withMain registers main).program = functions.program := rfl

/-- A source name and its function occupy the same position in the function table. -/
theorem Functions.declaration_lookup {functions : Functions} {index : Nat}
    {name : String} {f : Func} (h : functions.declarations[index]? = some (name, f)) :
    (functions.declarations.map Prod.fst)[index]? = some name ∧
      functions.program[index]? = some f := by
  simp [Functions.program, List.getElem?_map, h]

def Bundle.compile (bundle : Bundle) : Option Code :=
  LocalCompiler.compileChecked bundle.registers bundle.program bundle.main

/-- Named compilation has exactly the pre-existing compiler's acceptance and
generated code, with no alternative validity standard. -/
theorem Bundle.compile_some_iff (bundle : Bundle) (code : Code) :
    bundle.compile = some code ↔
      LocalCompiler.Valid bundle.registers bundle.program bundle.main ∧
        code = LocalCompiler.rawLink bundle.registers bundle.program bundle.main :=
  LocalCompiler.compileChecked_some_iff

/-- Pairing a name and body preserves their common position in the emitted
function table. This is the index that named calls use after resolution. -/
theorem Bundle.declaration_lookup {bundle : Bundle} {index : Nat} {name : String} {f : Func}
    (h : bundle.declarations[index]? = some (name, f)) :
    (bundle.declarations.map Prod.fst)[index]? = some name ∧
      bundle.program[index]? = some f := by
  simp [Bundle.program, List.getElem?_map, h]

/-- A resolved declaration is the actual compiled function at its linked
entry address, using the existing linker's proved layout theorem. -/
theorem Bundle.compiled_function {bundle : Bundle} {code : Code} {index : Nat}
    {name : String} {f : Func} (hcompile : bundle.compile = some code)
    (hdecl : bundle.declarations[index]? = some (name, f)) :
    CodeAt code (LocalCompiler.entry bundle.registers bundle.program bundle.main index)
      (LocalCompiler.compileFunc bundle.registers
        (LocalCompiler.calleeLocals bundle.program)
        (LocalCompiler.entry bundle.registers bundle.program bundle.main) f
        (LocalCompiler.entry bundle.registers bundle.program bundle.main index)) :=
  LocalCompiler.compileChecked_function hcompile (Bundle.declaration_lookup hdecl).2

end Ram.Named

namespace Ram.DSL

declare_syntax_cat ramDecl (behavior := symbol)

syntax &"fn " ident "(" ident,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : ramDecl

/-- A collection of callable functions, without a required main statement.
Calls share the same named function table, including recursive and forward calls. -/
syntax:max "ram_functions% " "{" ramDecl* "}" : term

/-- A complete named program. Function declarations share a function table;
each function and `main locals (...)` has its own independent variable table.
The global register bound is inferred from the largest local frame. -/
syntax:max "ram_program% " "{" ramDecl*
  &"main " ident "(" ident,* ")" "{" ramStmt* "}" "}" : term

private structure LoweredFunctions where
  declarations : Array (Lean.TSyntax `term)
  registers : Nat
  resolveFunction : FunctionResolver

/-- Both entry-point forms use the same two-pass function-name resolution and
the existing expression, statement and function lowering. -/
private def lowerFunctions (decls : Array (Lean.TSyntax `ramDecl)) :
    Lean.MacroM LoweredFunctions := do
  let mut functionNames : Array (Lean.Name × Nat) := #[]
  for decl in decls do
    match decl with
    | `(ramDecl| fn $name:ident($_params:ident,*) $_keyword:ident($_locals:ident,*) {
        $_body:ramStmt* return $_result:ramExpr; }) =>
        if functionNames.any (fun entry => entry.1 == name.getId) then
          Lean.Macro.throwErrorAt name "duplicate RAM function name"
        functionNames := functionNames.push (name.getId, functionNames.size)
    | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"
  let resolveFunction : FunctionResolver := fun name => do
    match functionNames.find? (fun entry => entry.1 == name.getId) with
    | some (_, index) =>
        let index := Lean.Syntax.mkNumLit (toString index)
        `($index:num)
    | none => Lean.Macro.throwErrorAt name "unknown RAM function name"
  let mut declarations : Array (Lean.TSyntax `term) := #[]
  let mut registers := 0
  for decl in decls do
    match decl with
    | `(ramDecl| fn $name:ident($params:ident,*) $keyword:ident($localNames:ident,*) {
        $body:ramStmt* return $result:ramExpr; }) =>
        let f ← lowerFunction Bool.true resolveFunction params.getElems localNames.getElems
          keyword body result
        let label := Lean.Syntax.mkStrLit name.getId.toString
        declarations := declarations.push (← `(($label:str, $f)))
        registers := max registers (params.getElems.size + localNames.getElems.size)
    | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"
  return ⟨declarations, registers, resolveFunction⟩

macro_rules
  | `(ram_functions% { $decls:ramDecl* }) => do
      let functions ← lowerFunctions decls
      let registerCount := Lean.Syntax.mkNumLit (toString functions.registers)
      let declarations := functions.declarations
      `(Ram.Named.Functions.mk $registerCount [$declarations,*])
  | `(ram_program% { $decls:ramDecl*
      main $mainLocals:ident ($mainNames:ident,*) { $mainBody:ramStmt* } }) => do
      if mainLocals.getId != `locals then
        Lean.Macro.throwErrorAt mainLocals "expected 'locals' followed by main's local register names"
      let functions ← lowerFunctions decls
      let mainScope ← makeLocalScope mainNames.getElems
      let main ← lowerBlock mainScope Bool.true functions.resolveFunction mainBody
      let registerCount := Lean.Syntax.mkNumLit
        (toString (max mainNames.getElems.size functions.registers))
      let declarations := functions.declarations
      `(Ram.Named.Bundle.mk $registerCount [$declarations,*] $main)

end Ram.DSL
