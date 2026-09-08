/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Basic
import Complexity.Computability.Ram.Source.Linking
import Complexity.Computability.Ram.Source.Syntax
import Complexity.Computability.Ram.Source.Named.Attributes

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
two array fields are passed. Handles can be parameters or typed lexical locals,
constructed from word expressions or borrowed from an existing handle. Their
two-word copies use the same local frame; no array allocation is implicit.

Results are words by default. `fn slice(...) : array` returns two fields and
`fn update(...) : Unit` returns none, using `return;` or `return ();`. Array
return expressions use the same handle/constructor/subslice forms as arguments.
`let window ← call slice(...)` infers an array binding from the signature and
allocates two actual receive slots; a Unit call allocates no result slot. All
returned expressions are evaluated before the callee frame is restored.

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

/-- Link an existing function collection under a source-name prefix. Only calls
in the right collection are relocated; its function bodies are not recompiled. -/
def Functions.link (left right : Functions) (namespacePrefix : String) : Functions where
  registers := max left.registers right.registers
  declarations := left.declarations ++ right.declarations.map fun (name, f) =>
    (namespacePrefix ++ "." ++ name, f.renameCalls (fun i => left.program.length + i))

@[simp] theorem Functions.link_program (left right : Functions) (namespacePrefix : String) :
    (left.link right namespacePrefix).program = Program.link left.program right.program := by
  simp [Functions.link, Functions.program, Program.link, List.map_map, Function.comp_def]

theorem Functions.embeds_link_left (left right : Functions) (namespacePrefix : String) :
    Program.Embeds id left.program (left.link right namespacePrefix).program := by
  rw [Functions.link_program]
  exact Program.embeds_link_left _ _

theorem Functions.embeds_link_right (left right : Functions) (namespacePrefix : String) :
    Program.Embeds (fun i => left.program.length + i) right.program
      (left.link right namespacePrefix).program := by
  rw [Functions.link_program]
  exact Program.embeds_link_right _ _

/-- Append functions whose calls already use the final table's indices.
In contrast to linking an independent module, these calls must not be relocated. -/
def Functions.extend (functions : Functions) (registers : Nat)
    (declarations : List Declaration) : Functions where
  registers := max functions.registers registers
  declarations := functions.declarations ++ declarations

@[simp] theorem Functions.extend_program (functions : Functions) (registers : Nat)
    (declarations : List Declaration) :
    (functions.extend registers declarations).program =
      functions.program ++ declarations.map Prod.snd := by
  simp [Functions.extend, Functions.program]

theorem Functions.embeds_extend (functions : Functions) (registers : Nat)
    (declarations : List Declaration) :
    Program.Embeds id functions.program (functions.extend registers declarations).program := by
  rw [Functions.extend_program]
  exact Program.embeds_append_left _ _

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
declare_syntax_cat ramInclude
declare_syntax_cat ramResultKind (behavior := symbol)

/-- Import an already declared function collection with qualified source names.
This form is resolved by `ram_def`, which retains declared parameter kinds. -/
syntax &"include " ident &" as " ident ";" : ramInclude

syntax ident : ramParam
syntax ident " : " &"array" : ramParam
syntax &"word" : ramResultKind
syntax &"array" : ramResultKind
syntax &"Unit" : ramResultKind

syntax &"fn " ident "(" ramParam,* ")" ident "(" ident,* ")" (" : " ramResultKind)? "{"
  ramStmt* "return " (ramExpr)? ";" "}" : ramDecl
syntax &"fn " ident "(" ramParam,* ")" (" : " ramResultKind)? "{"
  ramStmt* "return " (ramExpr)? ";" "}" : ramDecl

/-- A collection of callable functions, without a required main statement.
Calls share the same named function table, including recursive and forward calls. -/
syntax:max "ram_functions% " "{" ramInclude* ramDecl* "}" : term

/-- A complete named program. Function declarations share a function table;
each function and `main locals (...)` has its own independent variable table.
The global register bound is inferred from the largest local frame. -/
syntax:max "ram_program% " "{" ramInclude* ramDecl*
  &"main " ident "(" ident,* ")" "{" ramStmt* "}" "}" : term
syntax:max "ram_program% " "{" ramInclude* ramDecl*
  &"main " "{" ramStmt* "}" "}" : term

/-- A parsed function, shared by term quotations and proof-facing declarations. -/
structure FunctionDeclaration where
  name : Lean.TSyntax `ident
  params : Array Parameter
  locals : Array (Lean.TSyntax `ident)
  body : Array (Lean.TSyntax `ramStmt)
  result : Option (Lean.TSyntax `ramExpr)
  resultKind : ValueKind := .word
  deriving Inhabited

/-- Source-level signature metadata in function-table order. Physical word
arities do not determine whether parameters or results have array/Unit shape. -/
structure FunctionSignature where
  name : Lean.Name
  params : Array (Lean.Name × ValueKind)
  result : ValueKind := .word
  deriving Inhabited

/-- A resolved existing declaration and its retained source signatures. -/
structure FunctionImport where
  source : Lean.TSyntax `ident
  alias : Lean.TSyntax `ident
  signatures : Array FunctionSignature
  deriving Inhabited

/-- The common parsed form for term quotations and declaration elaboration. -/
structure ParsedNamed where
  includes : Array (Lean.TSyntax `ramInclude)
  declarations : Array (Lean.TSyntax `ramDecl)
  main : Option (Array (Lean.TSyntax `ident) × Array (Lean.TSyntax `ramStmt))

def parseNamed (source : Lean.TSyntax `term) : Lean.MacroM ParsedNamed := do
  match source with
  | `(ram_functions% { $imports:ramInclude* $decls:ramDecl* }) =>
      return ⟨imports, decls, none⟩
  | `(ram_program% { $imports:ramInclude* $decls:ramDecl*
      main $mainLocals:ident ($mainNames:ident,*) { $mainBody:ramStmt* } }) =>
      if mainLocals.getId != `locals then
        Lean.Macro.throwErrorAt mainLocals "expected 'locals' followed by main's local register names"
      return ⟨imports, decls, some (mainNames.getElems, mainBody)⟩
  | `(ram_program% { $imports:ramInclude* $decls:ramDecl*
      main { $mainBody:ramStmt* } }) =>
      return ⟨imports, decls, some (#[], mainBody)⟩
  | _ => Lean.Macro.throwErrorAt source "expected ram_functions% { ... } or ram_program% { ... }"

private def parseParameter (param : Lean.TSyntax `ramParam) : Lean.MacroM Parameter := do
  match param with
  | `(ramParam| $name:ident) => return ⟨name, .word⟩
  | `(ramParam| $name:ident : array) => return ⟨name, .array⟩
  | _ => Lean.Macro.throwErrorAt param "expected a word name or 'name : array'"

private def parseResultKind (kind : Option (Lean.TSyntax `ramResultKind)) :
    Lean.MacroM ValueKind := do
  let some kind := kind | return .word
  match kind with
  | `(ramResultKind| word) => return .word
  | `(ramResultKind| array) => return .array
  | `(ramResultKind| Unit) => return .unit
  | _ => Lean.Macro.throwErrorAt kind "expected word, array, or Unit"

private def parseFunction (decl : Lean.TSyntax `ramDecl) : Lean.MacroM FunctionDeclaration := do
  match decl with
  | `(ramDecl| fn $name:ident($params:ramParam,*) $keyword:ident($locals:ident,*)
      $[: $kind:ramResultKind]? { $body:ramStmt* return $[$result:ramExpr]?; }) =>
      if keyword.getId != `locals then
        Lean.Macro.throwErrorAt keyword "expected 'locals' followed by local register names"
      return ⟨name, ← params.getElems.mapM parseParameter, locals.getElems, body, result,
        ← parseResultKind kind⟩
  | `(ramDecl| fn $name:ident($params:ramParam,*) $[: $kind:ramResultKind]? {
      $body:ramStmt* return $[$result:ramExpr]?; }) =>
      return ⟨name, ← params.getElems.mapM parseParameter, #[], body, result,
        ← parseResultKind kind⟩
  | _ => Lean.Macro.throwErrorAt decl "expected a RAM function declaration"

private structure LoweredFunctions where
  declarations : Array (Lean.TSyntax `term)
  parsed : Array FunctionDeclaration
  scopes : Array LocalScope
  proofSites : Array (Array ProofSite)
  registers : Nat
  resolveFunction : FunctionResolver
  signatures : Array FunctionSignature

/-- Both entry-point forms collect function signatures before lowering bodies.
Array parameters are flattened only at declared array argument positions. -/
private def lowerFunctions (decls : Array (Lean.TSyntax `ramDecl))
    (imported : Array FunctionSignature) :
    Lean.MacroM LoweredFunctions := do
  let parsed ← decls.mapM parseFunction
  let mut signatures := imported
  for decl in parsed do
    if signatures.any (fun entry => entry.name == decl.name.getId) then
      Lean.Macro.throwErrorAt decl.name "duplicate RAM function name"
    signatures := signatures.push ⟨decl.name.getId,
      decl.params.map (fun param => (param.name.getId, param.kind)), decl.resultKind⟩
  let resolveFunction : FunctionResolver := fun scope strict name args => do
    match signatures.findIdx? (fun entry => entry.name == name.getId) with
    | some index =>
        let params := signatures[index]!.params
        if args.size != params.size then
          Lean.Macro.throwErrorAt name "wrong number of RAM function arguments"
        let mut lowered := #[]
        for (param, arg) in params.zip args do
          lowered := lowered ++ (← valueArgument scope strict param.2 arg)
        let literal := Lean.Syntax.mkNumLit (toString index)
        return (← `($literal:num), lowered, signatures[index]!.result)
    | none => Lean.Macro.throwErrorAt name "unknown RAM function name"
  let mut declarations : Array (Lean.TSyntax `term) := #[]
  let mut scopes := #[]
  let mut proofSites := #[]
  let mut registers := 0
  for decl in parsed do
    let f ← lowerFunctionWithScope Bool.true resolveFunction decl.params decl.locals
      decl.body decl.result decl.resultKind
    let label := Lean.Syntax.mkStrLit decl.name.getId.toString
    declarations := declarations.push (← `(($label:str, $(f.term))))
    scopes := scopes.push f.scope
    proofSites := proofSites.push f.proofSites
    registers := max registers f.registers
  return ⟨declarations, parsed, scopes, proofSites, registers, resolveFunction, signatures⟩

/-- One named lowering, retaining the bindings needed by `ram_def`. -/
structure LoweredNamed where
  type : Lean.TSyntax `term
  term : Lean.TSyntax `term
  parsed : Array FunctionDeclaration
  functions : Array (Lean.TSyntax `term)
  functionScopes : Array LocalScope
  functionProofSites : Array (Array ProofSite)
  mainScope : LocalScope
  mainProofSites : Array ProofSite
  imports : Array FunctionImport
  prefixes : Array (Lean.TSyntax `term)
  signatures : Array FunctionSignature
  localOffset : Nat
  localRegisters : Nat

/-- Quotation and command forms share this single lowering, including allocation
of lexical locals and the inferred maximum frame size. -/
def lowerNamed (source : Lean.TSyntax `term) (imports : Array FunctionImport := #[]) :
    Lean.MacroM LoweredNamed := do
  let parsed ← parseNamed source
  if parsed.includes.size != imports.size then
    Lean.Macro.throwErrorAt source "use 'ram_def' to resolve included function declarations"
  let mut imported : Array FunctionSignature := #[]
  let mut aliases : Array Lean.Name := #[]
  let mut linkedPrefix ← `(Ram.Named.Functions.mk 0 [])
  let mut prefixes := #[linkedPrefix]
  for dependency in imports do
    if aliases.contains dependency.alias.getId then
      Lean.Macro.throwErrorAt dependency.alias "duplicate RAM import alias"
    aliases := aliases.push dependency.alias.getId
    for signature in dependency.signatures do
      imported := imported.push { signature with name := dependency.alias.getId ++ signature.name }
    let label := Lean.Syntax.mkStrLit dependency.alias.getId.toString
    let src := dependency.source
    linkedPrefix ← `(Ram.Named.Functions.link $linkedPrefix
      (Ram.Named.Functions.mk ($src:ident).registers ($src:ident).declarations) $label:str)
    prefixes := prefixes.push linkedPrefix
  let functions ← lowerFunctions parsed.declarations imported
  let declarations := functions.declarations
  let registerCount := Lean.Syntax.mkNumLit (toString functions.registers)
  let collection ← if imports.isEmpty then
      `(Ram.Named.Functions.mk $registerCount [$declarations,*])
    else `(Ram.Named.Functions.extend $linkedPrefix $registerCount [$declarations,*])
  let type ← `(Ram.Named.Functions)
  let base : LoweredNamed := {
    type := type
    term := collection
    parsed := functions.parsed
    functions := declarations
    functionScopes := functions.scopes
    functionProofSites := functions.proofSites
    mainScope := #[]
    mainProofSites := #[]
    imports := imports
    prefixes := prefixes
    signatures := functions.signatures
    localOffset := imported.size
    localRegisters := functions.registers }
  match parsed.main with
  | none =>
      return base
  | some (names, body) =>
      let scope ← makeLocalScope names
      let main ← lowerScopedBlock scope #[] (localRegisterCount scope)
        Bool.true functions.resolveFunction body
      let registerCount := Lean.Syntax.mkNumLit
        (toString (max main.nextRegister functions.registers))
      let term ← if imports.isEmpty then
          `(Ram.Named.Bundle.mk $registerCount [$declarations,*] $(main.term))
        else `(($collection).withMain $registerCount $(main.term))
      let type ← `(Ram.Named.Bundle)
      return { base with
        type := type
        term := term
        mainScope := main.scope
        mainProofSites := main.proofSites }

macro_rules
  | `(ram_functions% { $imports:ramInclude* $decls:ramDecl* }) => do
      return (← lowerNamed (← `(ram_functions% { $imports:ramInclude* $decls:ramDecl* }))).term
  | `(ram_program% { $imports:ramInclude* $decls:ramDecl*
      main $locals:ident ($names:ident,*) { $body:ramStmt* } }) => do
      return (← lowerNamed (← `(ram_program% { $imports:ramInclude* $decls:ramDecl*
        main $locals:ident ($names:ident,*) { $body:ramStmt* } }))).term
  | `(ram_program% { $imports:ramInclude* $decls:ramDecl* main { $body:ramStmt* } }) => do
      return (← lowerNamed (← `(ram_program% { $imports:ramInclude* $decls:ramDecl*
        main { $body:ramStmt* } }))).term

end Ram.DSL
