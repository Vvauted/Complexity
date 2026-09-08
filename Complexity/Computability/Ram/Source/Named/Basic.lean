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

A bare parameter is a word; `xs : array` declares a base-and-length handle.
Its fields are word locals, and `xs[i]` performs the existing word load.
At `call f(xs)`, the declared signature determines whether one word or the
two array fields are passed. Handles currently originate from function
parameters, not allocation or a general array-valued local-binding syntax.

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
declare_syntax_cat ramParam

syntax ident : ramParam
syntax ident " : " &"array" : ramParam

syntax &"fn " ident "(" ramParam,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : ramDecl
syntax &"fn " ident "(" ramParam,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : ramDecl

/-- A collection of callable functions, without a required main statement.
Calls share the same named function table, including recursive and forward calls. -/
syntax:max "ram_functions% " "{" ramDecl* "}" : term

/-- A complete named program. Function declarations share a function table;
each function and `main locals (...)` has its own independent variable table.
The global register bound is inferred from the largest local frame. -/
syntax:max "ram_program% " "{" ramDecl*
  &"main " ident "(" ident,* ")" "{" ramStmt* "}" "}" : term
syntax:max "ram_program% " "{" ramDecl*
  &"main " "{" ramStmt* "}" "}" : term

/-- A parsed function, shared by term quotations and proof-facing declarations. -/
structure FunctionDeclaration where
  name : Lean.TSyntax `ident
  params : Array Parameter
  locals : Array (Lean.TSyntax `ident)
  body : Array (Lean.TSyntax `ramStmt)
  result : Lean.TSyntax `ramExpr
  deriving Inhabited

private def parseParameter (param : Lean.TSyntax `ramParam) : Lean.MacroM Parameter := do
  match param with
  | `(ramParam| $name:ident) => return ⟨name, .word⟩
  | `(ramParam| $name:ident : array) => return ⟨name, .array⟩
  | _ => Lean.Macro.throwErrorAt param "expected a word name or 'name : array'"

private def parseFunction (decl : Lean.TSyntax `ramDecl) : Lean.MacroM FunctionDeclaration := do
  match decl with
  | `(ramDecl| fn $name:ident($params:ramParam,*) $keyword:ident($locals:ident,*) {
      $body:ramStmt* return $result:ramExpr; }) =>
      if keyword.getId != `locals then
        Lean.Macro.throwErrorAt keyword "expected 'locals' followed by local register names"
      return ⟨name, ← params.getElems.mapM parseParameter, locals.getElems, body, result⟩
  | `(ramDecl| fn $name:ident($params:ramParam,*) { $body:ramStmt* return $result:ramExpr; }) =>
      return ⟨name, ← params.getElems.mapM parseParameter, #[], body, result⟩
  | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"

private structure LoweredFunctions where
  declarations : Array (Lean.TSyntax `term)
  parsed : Array FunctionDeclaration
  scopes : Array LocalScope
  registers : Nat
  resolveFunction : FunctionResolver

/-- Both entry-point forms collect function signatures before lowering bodies.
Array parameters are flattened only at declared array argument positions. -/
private def lowerFunctions (decls : Array (Lean.TSyntax `ramDecl)) :
    Lean.MacroM LoweredFunctions := do
  let parsed ← decls.mapM parseFunction
  let mut functionNames : Array (Lean.Name × Nat) := #[]
  for decl in parsed do
    if functionNames.any (fun entry => entry.1 == decl.name.getId) then
      Lean.Macro.throwErrorAt decl.name "duplicate RAM function name"
    functionNames := functionNames.push (decl.name.getId, functionNames.size)
  let resolveFunction : FunctionResolver := fun scope strict name args => do
    match functionNames.find? (fun entry => entry.1 == name.getId) with
    | some (_, index) =>
        let params := parsed[index]!.params
        if args.size != params.size then
          Lean.Macro.throwErrorAt name "wrong number of RAM function arguments"
        let mut lowered := #[]
        for (param, arg) in params.zip args do
          match param.kind with
          | .word => lowered := lowered.push (← lowerExpr scope strict arg)
          | .array => lowered := lowered ++ (← arrayArgument scope arg)
        let literal := Lean.Syntax.mkNumLit (toString index)
        return (← `($literal:num), lowered)
    | none => Lean.Macro.throwErrorAt name "unknown RAM function name"
  let mut declarations : Array (Lean.TSyntax `term) := #[]
  let mut scopes := #[]
  let mut registers := 0
  for decl in parsed do
    let f ← lowerFunctionWithScope Bool.true resolveFunction decl.params decl.locals
      decl.body decl.result
    let label := Lean.Syntax.mkStrLit decl.name.getId.toString
    declarations := declarations.push (← `(($label:str, $(f.term))))
    scopes := scopes.push f.scope
    registers := max registers f.registers
  return ⟨declarations, parsed, scopes, registers, resolveFunction⟩

/-- One named lowering, retaining the bindings needed by `ram_def`. -/
structure LoweredNamed where
  type : Lean.TSyntax `term
  term : Lean.TSyntax `term
  parsed : Array FunctionDeclaration
  functions : Array (Lean.TSyntax `term)
  functionScopes : Array LocalScope
  mainScope : LocalScope

/-- Quotation and command forms share this single lowering, including allocation
of lexical locals and the inferred maximum frame size. -/
def lowerNamed (source : Lean.TSyntax `term) : Lean.MacroM LoweredNamed := do
  let (decls, main) ← match source with
    | `(ram_functions% { $decls:ramDecl* }) => pure (decls, none)
    | `(ram_program% { $decls:ramDecl*
        main $mainLocals:ident ($mainNames:ident,*) { $mainBody:ramStmt* } }) => do
      if mainLocals.getId != `locals then
        Lean.Macro.throwErrorAt mainLocals "expected 'locals' followed by main's local register names"
      pure (decls, some (mainNames.getElems, mainBody))
    | `(ram_program% { $decls:ramDecl* main { $mainBody:ramStmt* } }) =>
        pure (decls, some (#[], mainBody))
    | _ =>
      Lean.Macro.throwErrorAt source
        "expected ram_functions% { ... } or ram_program% { ... }"
  let functions ← lowerFunctions decls
  let declarations := functions.declarations
  match main with
  | none =>
      let registerCount := Lean.Syntax.mkNumLit (toString functions.registers)
      let term ← `(Ram.Named.Functions.mk $registerCount [$declarations,*])
      return ⟨← `(Ram.Named.Functions), term, functions.parsed, declarations, functions.scopes, #[]⟩
  | some (names, body) =>
      let scope ← makeLocalScope names
      let main ← lowerScopedBlock scope #[] (localRegisterCount scope)
        Bool.true functions.resolveFunction body
      let registerCount := Lean.Syntax.mkNumLit
        (toString (max main.nextRegister functions.registers))
      let term ← `(Ram.Named.Bundle.mk $registerCount [$declarations,*] $(main.term))
      return ⟨← `(Ram.Named.Bundle), term, functions.parsed, declarations,
        functions.scopes, main.scope⟩

macro_rules
  | `(ram_functions% { $decls:ramDecl* }) => do
      return (← lowerNamed (← `(ram_functions% { $decls:ramDecl* }))).term
  | `(ram_program% { $decls:ramDecl*
      main $locals:ident ($names:ident,*) { $body:ramStmt* } }) => do
      return (← lowerNamed (← `(ram_program% { $decls:ramDecl*
        main $locals:ident ($names:ident,*) { $body:ramStmt* } }))).term
  | `(ram_program% { $decls:ramDecl* main { $body:ramStmt* } }) => do
      return (← lowerNamed (← `(ram_program% { $decls:ramDecl*
        main { $body:ramStmt* } }))).term

end Ram.DSL
