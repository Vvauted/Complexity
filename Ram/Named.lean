import Ram.Syntax
import Ram.Compiler

/-!
# Named programs over the existing RAM language

`ram_program%` collects all function names before lowering any body. A call
can therefore refer forward, recurse, or participate in mutual recursion.
Functions and local variables have separate name tables. Embedded `const(t)`
terms retain the enclosing Lean scope and never refer to runtime registers.

The result contains only an ordinary `Program`, its names as metadata, and a
main statement. `Bundle.compile` is the existing checked compiler: arity and
register validity are not redefined here. Duplicate/unknown function names and
undeclared variables are reported while resolving the surface syntax.
-/

namespace Ram.Named

abbrev Declaration := String × Func

/-- Function names remain paired with their bodies for readable inspection.
They are not runtime strings or a new instruction-level lookup operation. -/
structure Bundle where
  registers : Nat
  declarations : List Declaration
  main : Stmt
  deriving DecidableEq, Repr

def Bundle.program (bundle : Bundle) : Program := bundle.declarations.map Prod.snd

def Bundle.compile (bundle : Bundle) : Option Code :=
  Compiler.compileChecked bundle.registers bundle.program bundle.main

/-- Named compilation has exactly the pre-existing compiler's acceptance and
generated code, with no alternative validity standard. -/
theorem Bundle.compile_some_iff (bundle : Bundle) (code : Code) :
    bundle.compile = some code ↔
      Compiler.Valid bundle.registers bundle.program bundle.main ∧
        code = Compiler.rawLink bundle.registers bundle.program bundle.main :=
  Compiler.compileChecked_some_iff

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
    CodeAt code (Compiler.entry bundle.registers bundle.program bundle.main index)
      (Compiler.compileFunc bundle.registers
        (Compiler.entry bundle.registers bundle.program bundle.main) f
        (Compiler.entry bundle.registers bundle.program bundle.main index)) :=
  Compiler.compileChecked_function hcompile (Bundle.declaration_lookup hdecl).2

end Ram.Named

namespace Ram.DSL

declare_syntax_cat ramDecl (behavior := symbol)

syntax &"fn " ident "(" ident,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : ramDecl

/-- A complete named program. Function declarations share a function table;
each function and `main locals (...)` has its own independent variable table.
The global register bound is inferred from the largest local frame. -/
syntax:max "ram_program% " "{" ramDecl*
  &"main " ident "(" ident,* ")" "{" ramStmt* "}" "}" : term

macro_rules
  | `(ram_program% { $decls:ramDecl*
      main $mainLocals:ident ($mainNames:ident,*) { $mainBody:ramStmt* } }) => do
      if mainLocals.getId != `locals then
        Lean.Macro.throwErrorAt mainLocals "expected 'locals' followed by main's local register names"
      -- The first pass establishes the whole table, before any call is resolved.
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
      let mut registers := mainNames.getElems.size
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
      let mainScope ← makeLocalScope mainNames.getElems
      let main ← lowerBlock mainScope Bool.true resolveFunction mainBody
      let registerCount := Lean.Syntax.mkNumLit (toString registers)
      `(Ram.Named.Bundle.mk $registerCount [$declarations,*] $main)

end Ram.DSL

namespace Ram.Named.Examples

/-- Forward and mutual references are resolved once. Local `even` has the same
spelling as a function, but reading it and calling it use separate tables. -/
def parity : Bundle := ram_program% {
  fn even(n) locals (answer) {
    if n {
      answer := call odd(n - 1);
    } else {
      answer := 1;
    }
    return answer;
  }
  fn odd(even) locals (answer) {
    if even {
      answer := call even(even - 1);
    } else {
      answer := 0;
    }
    return answer;
  }
  main locals (input, answer) {
    read input;
    answer := call even(input);
    write answer;
  }
}

/-- The forward call and the same-spelling call both have the intended static
targets; their arguments still read each function's parameter register. -/
theorem parity_expands : parity =
    { registers := 2
      declarations :=
        [("even", ⟨1, 2,
          .ite (.var 0) (.call 1 1 [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.const 1)), .var 1⟩),
         ("odd", ⟨1, 2,
          .ite (.var 0) (.call 1 0 [.bin .sub (.var 0) (.const 1)])
            (.assign 1 (.const 0)), .var 1⟩)]
      main := .seq (.read 0) (.seq (.call 1 0 [.var 0]) (.write (.var 1))) } := rfl

theorem parity_valid : Compiler.Valid parity.registers parity.program parity.main := by decide

theorem parity_compiles : parity.compile =
    some (Compiler.rawLink parity.registers parity.program parity.main) :=
  (Bundle.compile_some_iff _ _).mpr ⟨parity_valid, rfl⟩

/-- The same recursive declaration can be written without maintaining a `self`
number; its own name is already present when the body is lowered. -/
def recursive : Bundle := ram_program% {
  fn factorial(n) locals (answer) {
    if n {
      answer := call factorial(n - 1);
      answer := n * answer;
    } else {
      answer := 1;
    }
    return answer;
  }
  main locals (n, answer) {
    read n;
    answer := call factorial(n);
    write answer;
  }
}

theorem recursive_body : (recursive.program[0]?).map Func.body =
    some (.ite (.var 0)
      (.seq (.call 1 0 [.bin .sub (.var 0) (.const 1)])
        (.assign 1 (.bin .mul (.var 0) (.var 1))))
      (.assign 1 (.const 1))) := rfl

end Ram.Named.Examples
