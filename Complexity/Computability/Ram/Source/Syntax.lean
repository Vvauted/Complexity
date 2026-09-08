/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.ForIn
import Lean

/-!
# A surface language for the verified RAM AST

`ram_expr%` quotes an expression, `ram% { ... }` quotes a statement block, and
`ram_fun% (parameters) { ... return expression; }` quotes a function. Its locals
can be introduced with `let`, `let mut`, or a call-result binding. The explicit
`locals (locals)` header is also supported. Function syntax assigns local register numbers only at
variable occurrences, not by introducing Lean bindings around the body.
Outside that syntax, identifiers refer to ordinary Lean bindings of type
`Ram.Reg`; legacy call targets refer to Lean `Nat` bindings. Function targets
and `const(t)` retain their enclosing Lean scope, even when a parameter has
the same spelling. `Complexity.Computability.Ram.Source.Named.Basic` adds a
separately resolved named function table.

Named functions additionally support `xs : array` parameters. A handle occupies
two ordinary word parameters, exposed as `xs.base` and `xs.length`; `xs[i]`
loads from its base. Named calls check the declared parameter kinds and pass
both fields for an array argument. An array handle is not a word expression.
The standalone `ram_fun%` form and lexical `let` bindings remain word-valued.
`for x in xs { ... }` traverses a named array parameter. It copies the base and
length into fresh cursor locals and loads an immutable `x` for each iteration;
the generated cursor updates do not modify the array descriptor. Elements are
read from memory at each iteration, not snapshotted before the loop.

Lexical declarations allocate fresh frame slots, including when shadowing an
outer name. An initializer sees the previous scope; branch and loop bindings
do not escape their blocks. `let` bindings reject later assignment, while
parameters, header locals and `let mut` bindings are mutable. Allocation is
static: a loop-local initializer executes again each iteration, without growing
the frame. Raw `ram%` and `ram_stmt%` have no function frame to allocate and
continue to use caller-provided register names.

The macros produce only the existing `Expr`, `Stmt`, and `Func` constructors.
There is no host-language callback, implicit bulk operation, cost annotation,
or alternate evaluator. `const(t)` embeds a compile-time natural constant;
plain identifiers always read registers. Array indexing is the existing word
addition followed by one-word load, and `a[i] := e` is its one-word store form.

Arithmetic retains unsigned machine-word semantics, including wrapping
subtraction, unsigned division/remainder, and logical shifts. `&&&`, `|||`, and
`^^^` are bitwise operations, not short-circuit Boolean operators. A condition
uses the existing zero/nonzero convention. A `return` occurs only at the end
of a function, matching `Func.result`; this syntax does not pretend that the
current statement AST has early returns, break, or continue.
-/

namespace Ram.DSL

declare_syntax_cat ramExpr

syntax:max num : ramExpr
syntax:max ident : ramExpr
syntax:max "(" ramExpr ")" : ramExpr
syntax:max "const(" term ")" : ramExpr
syntax:max "load[" ramExpr "]" : ramExpr
syntax:max "true" : ramExpr
syntax:max "false" : ramExpr
syntax:100 ramExpr:100 "[" ramExpr "]" : ramExpr
syntax:80 "!" ramExpr:80 : ramExpr
syntax:80 "-" ramExpr:80 : ramExpr
syntax:70 ramExpr " * " ramExpr:71 : ramExpr
syntax:70 ramExpr " / " ramExpr:71 : ramExpr
syntax:70 ramExpr " % " ramExpr:71 : ramExpr
syntax:65 ramExpr " + " ramExpr:66 : ramExpr
syntax:65 ramExpr " - " ramExpr:66 : ramExpr
syntax:60 ramExpr " << " ramExpr:61 : ramExpr
syntax:60 ramExpr " >> " ramExpr:61 : ramExpr
syntax:55 ramExpr " &&& " ramExpr:56 : ramExpr
syntax:54 ramExpr " ^^^ " ramExpr:55 : ramExpr
syntax:53 ramExpr " ||| " ramExpr:54 : ramExpr
syntax:50 ramExpr:51 " == " ramExpr:51 : ramExpr
syntax:50 ramExpr:51 " != " ramExpr:51 : ramExpr
syntax:50 ramExpr:51 " < " ramExpr:51 : ramExpr
syntax:50 ramExpr:51 " <= " ramExpr:51 : ramExpr
syntax:50 ramExpr:51 " > " ramExpr:51 : ramExpr
syntax:50 ramExpr:51 " >= " ramExpr:51 : ramExpr

/-- Quote a RAM expression; identifiers denote registers and numerals denote
word constants. The result is the existing `Ram.Expr` AST. -/
syntax:max "ram_expr% " ramExpr : term

declare_syntax_cat ramStmt

syntax "skip" ";" : ramStmt
syntax ident " := " ramExpr ";" : ramStmt
syntax ident " += " ramExpr ";" : ramStmt
syntax ident " -= " ramExpr ";" : ramStmt
syntax ident " *= " ramExpr ";" : ramStmt
syntax ident "[" ramExpr "]" " := " ramExpr ";" : ramStmt
syntax "store[" ramExpr "]" " := " ramExpr ";" : ramStmt
syntax "read " ident ";" : ramStmt
syntax "write " ramExpr ";" : ramStmt
syntax ident " := " "call " ident "(" ramExpr,* ")" ";" : ramStmt
/-- Bind a fresh immutable word local for the rest of the enclosing block. -/
syntax "let " ident " := " ramExpr ";" : ramStmt
/-- Bind a fresh mutable word local for the rest of the enclosing block. -/
syntax "let " "mut " ident " := " ramExpr ";" : ramStmt
/-- Bind the result of a real source call, not a host-language computation. -/
syntax "let " ident " ← " "call " ident "(" ramExpr,* ")" ";" : ramStmt
syntax "let " "mut " ident " ← " "call " ident "(" ramExpr,* ")" ";" : ramStmt
syntax "if " ramExpr " {" ramStmt* "}" : ramStmt
syntax "if " ramExpr " {" ramStmt* "}" " else " "{" ramStmt* "}" : ramStmt
syntax "while " ramExpr " {" ramStmt* "}" : ramStmt
/-- Traverse a typed array parameter with an immutable block-local element. -/
syntax "for " ident " in " ident " {" ramStmt* "}" : ramStmt

/-- Quote a RAM statement block. Braces delimit control-flow bodies; atomic
statements end in semicolons. Empty blocks are `Stmt.skip`. -/
syntax:max "ram% " "{" ramStmt* "}" : term

/-- Quote a single surface statement. Usually used through `ram% { ... }`. -/
syntax:max "ram_stmt% " ramStmt : term

/- The bound-variable translator deliberately visits only RAM variable
positions. In particular it never rewrites a call target or the Lean term
inside `const(...)`. This keeps the three namespaces independent. -/

/-- Source parameter shape; an array is a two-word by-value handle. -/
inductive ParameterKind where
  | word
  | array
  deriving BEq, Inhabited

/-- A declared parameter before local-register allocation. -/
structure Parameter where
  name : Lean.TSyntax `ident
  kind : ParameterKind := .word
  deriving Inhabited

/-- One lexical binding and the first register of its representation. -/
structure LocalBinding where
  name : Lean.Name
  register : Nat
  kind : ParameterKind := .word
  deriving Inhabited

abbrev LocalScope := Array LocalBinding

/-- Resolve a call using its signature and the caller's lexical bindings. -/
abbrev FunctionResolver := LocalScope → Bool → Lean.TSyntax `ident →
  Array (Lean.TSyntax `ramExpr) →
    Lean.MacroM (Lean.TSyntax `term × Array (Lean.TSyntax `term))

def localRegisterCount (scope : LocalScope) : Nat :=
  scope.foldl (fun count binding =>
    max count (binding.register + if binding.kind == .array then 2 else 1)) 0

def makeParameterScope (params : Array Parameter) : Lean.MacroM LocalScope := do
  let mut scope : LocalScope := #[]
  for param in params do
    let name := param.name.getId
    if scope.any (fun entry => entry.name == name ||
        (entry.kind == .array &&
          (name == entry.name ++ `base || name == entry.name ++ `length)) ||
        (param.kind == .array &&
          (entry.name == name ++ `base || entry.name == name ++ `length))) then
      Lean.Macro.throwErrorAt param.name "duplicate RAM parameter or local name"
    scope := scope.push ⟨name, localRegisterCount scope, param.kind⟩
  return scope

def makeLocalScope (names : Array (Lean.TSyntax `ident)) : Lean.MacroM LocalScope := do
  makeParameterScope (names.map fun name => ⟨name, .word⟩)

private def registerTerm (index : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
  let index := Lean.Syntax.mkNumLit (toString index)
  `($index:num)

private def arrayField? (scope : LocalScope) (name : Lean.Name) : Option Nat := do
  let .str parent field := name | none
  let binding ← scope.find? (fun entry => entry.name == parent && entry.kind == .array)
  match field with
  | "base" => some binding.register
  | "length" => some (binding.register + 1)
  | _ => none

def resolveLocal (scope : LocalScope) (strict : Bool) (name : Lean.TSyntax `ident) :
    Lean.MacroM (Lean.TSyntax `term) := do
  match scope.find? (fun entry => entry.name == name.getId) with
  | some binding =>
      if binding.kind == .array then
        Lean.Macro.throwErrorAt name "expected a word; use an array field or indexed element"
      registerTerm binding.register
  | none =>
      if let some index := arrayField? scope name.getId then
        return ← registerTerm index
      if strict then
        Lean.Macro.throwErrorAt name "unknown RAM local variable"
      else
        `($name:ident)

/-- Array indexing uses the descriptor's base word; scalar pointer indexing
remains available for existing source programs. -/
private def resolveBase (scope : LocalScope) (strict : Bool) (name : Lean.TSyntax `ident) :
    Lean.MacroM (Lean.TSyntax `term) := do
  match scope.find? (fun entry => entry.name == name.getId && entry.kind == .array) with
  | some binding => registerTerm binding.register
  | none => resolveLocal scope strict name

partial def arrayArgument (scope : LocalScope) (expr : Lean.TSyntax `ramExpr) :
    Lean.MacroM (Array (Lean.TSyntax `term)) := do
  match expr with
  | `(ramExpr| ($arg:ramExpr)) => arrayArgument scope arg
  | `(ramExpr| $name:ident) =>
      match scope.find? (fun entry => entry.name == name.getId && entry.kind == .array) with
      | some binding =>
          return #[← `(Ram.Expr.var $(← registerTerm binding.register)),
            ← `(Ram.Expr.var $(← registerTerm (binding.register + 1)))]
      | none => Lean.Macro.throwErrorAt name "expected an array parameter"
  | _ => Lean.Macro.throwErrorAt expr "expected an array parameter"

partial def lowerExpr (scope : LocalScope) (strict : Bool)
    (expr : Lean.TSyntax `ramExpr) : Lean.MacroM (Lean.TSyntax `term) := do
  let binary (op : Lean.TSyntax `term) (a b : Lean.TSyntax `ramExpr) := do
    let a ← lowerExpr scope strict a
    let b ← lowerExpr scope strict b
    `(Ram.Expr.bin $op $a $b)
  match expr with
  | `(ramExpr| $n:num) => `(Ram.Expr.const $n)
  | `(ramExpr| $x:ident) => `(Ram.Expr.var $(← resolveLocal scope strict x))
  | `(ramExpr| ($e:ramExpr)) => lowerExpr scope strict e
  | `(ramExpr| const($n:term)) => `(Ram.Expr.const $n)
  | `(ramExpr| load[$a:ramExpr]) => `(Ram.Expr.load $(← lowerExpr scope strict a))
  | `(ramExpr| true) => `(Ram.Expr.const 1)
  | `(ramExpr| false) => `(Ram.Expr.const 0)
  | `(ramExpr| $a:ident[$i:ramExpr]) =>
      `(Ram.Expr.index (Ram.Expr.var $(← resolveBase scope strict a))
        $(← lowerExpr scope strict i))
  | `(ramExpr| $a:ramExpr[$i:ramExpr]) =>
      `(Ram.Expr.index $(← lowerExpr scope strict a) $(← lowerExpr scope strict i))
  | `(ramExpr| !$e:ramExpr) =>
      `(Ram.Expr.bin .eq $(← lowerExpr scope strict e) (Ram.Expr.const 0))
  | `(ramExpr| -$e:ramExpr) =>
      `(Ram.Expr.bin .sub (Ram.Expr.const 0) $(← lowerExpr scope strict e))
  | `(ramExpr| $a:ramExpr + $b:ramExpr) => binary (← `(Ram.BinOp.add)) a b
  | `(ramExpr| $a:ramExpr - $b:ramExpr) => binary (← `(Ram.BinOp.sub)) a b
  | `(ramExpr| $a:ramExpr * $b:ramExpr) => binary (← `(Ram.BinOp.mul)) a b
  | `(ramExpr| $a:ramExpr / $b:ramExpr) => binary (← `(Ram.BinOp.udiv)) a b
  | `(ramExpr| $a:ramExpr % $b:ramExpr) => binary (← `(Ram.BinOp.umod)) a b
  | `(ramExpr| $a:ramExpr << $b:ramExpr) => binary (← `(Ram.BinOp.shl)) a b
  | `(ramExpr| $a:ramExpr >> $b:ramExpr) => binary (← `(Ram.BinOp.shr)) a b
  | `(ramExpr| $a:ramExpr &&& $b:ramExpr) => binary (← `(Ram.BinOp.band)) a b
  | `(ramExpr| $a:ramExpr ^^^ $b:ramExpr) => binary (← `(Ram.BinOp.bxor)) a b
  | `(ramExpr| $a:ramExpr ||| $b:ramExpr) => binary (← `(Ram.BinOp.bor)) a b
  | `(ramExpr| $a:ramExpr == $b:ramExpr) => binary (← `(Ram.BinOp.eq)) a b
  | `(ramExpr| $a:ramExpr != $b:ramExpr) =>
      `(Ram.Expr.bin .eq $(← binary (← `(Ram.BinOp.eq)) a b) (Ram.Expr.const 0))
  | `(ramExpr| $a:ramExpr < $b:ramExpr) => binary (← `(Ram.BinOp.ult)) a b
  | `(ramExpr| $a:ramExpr <= $b:ramExpr) => binary (← `(Ram.BinOp.ule)) a b
  | `(ramExpr| $a:ramExpr > $b:ramExpr) => binary (← `(Ram.BinOp.ult)) b a
  | `(ramExpr| $a:ramExpr >= $b:ramExpr) => binary (← `(Ram.BinOp.ule)) b a
  | _ => Lean.Macro.throwErrorAt expr "unsupported RAM expression"

def externalFunction : FunctionResolver := fun scope strict name args => do
  return (← `($name:ident), ← args.mapM (lowerExpr scope strict))

mutual
partial def lowerStmt (scope : LocalScope) (strict : Bool) (function : FunctionResolver)
    (stmt : Lean.TSyntax `ramStmt) : Lean.MacroM (Lean.TSyntax `term) := do
  let resolveVar := resolveLocal scope strict
  let expr := lowerExpr scope strict
  let block := lowerBlock scope strict function
  match stmt with
  | `(ramStmt| skip;) => `(Ram.Stmt.skip)
  | `(ramStmt| $x:ident := $e:ramExpr;) => `(Ram.Stmt.assign $(← resolveVar x) $(← expr e))
  | `(ramStmt| $x:ident += $e:ramExpr;) =>
      let x ← resolveVar x
      `(Ram.Stmt.assign $x (Ram.Expr.bin .add (Ram.Expr.var $x) $(← expr e)))
  | `(ramStmt| $x:ident -= $e:ramExpr;) =>
      let x ← resolveVar x
      `(Ram.Stmt.assign $x (Ram.Expr.bin .sub (Ram.Expr.var $x) $(← expr e)))
  | `(ramStmt| $x:ident *= $e:ramExpr;) =>
      let x ← resolveVar x
      `(Ram.Stmt.assign $x (Ram.Expr.bin .mul (Ram.Expr.var $x) $(← expr e)))
  | `(ramStmt| $a:ident[$i:ramExpr] := $e:ramExpr;) =>
      `(Ram.Stmt.store (Ram.Expr.bin .add
        (Ram.Expr.var $(← resolveBase scope strict a)) $(← expr i)) $(← expr e))
  | `(ramStmt| store[$a:ramExpr] := $e:ramExpr;) => `(Ram.Stmt.store $(← expr a) $(← expr e))
  | `(ramStmt| read $x:ident;) => `(Ram.Stmt.read $(← resolveVar x))
  | `(ramStmt| write $e:ramExpr;) => `(Ram.Stmt.write $(← expr e))
  | `(ramStmt| $x:ident := call $f:ident($args:ramExpr,*);) =>
      let (fn, es) ← function scope strict f args.getElems
      `(Ram.Stmt.call $(← resolveVar x) $fn [$es,*])
  | `(ramStmt| if $c:ramExpr { $yes:ramStmt* }) =>
      `(Ram.Stmt.ite $(← expr c) $(← block yes) Ram.Stmt.skip)
  | `(ramStmt| if $c:ramExpr { $yes:ramStmt* } else { $no:ramStmt* }) =>
      `(Ram.Stmt.ite $(← expr c) $(← block yes) $(← block no))
  | `(ramStmt| while $c:ramExpr { $body:ramStmt* }) =>
      `(Ram.Stmt.while $(← expr c) $(← block body))
  | `(ramStmt| for $_element:ident in $_array:ident { $_body:ramStmt* }) =>
      Lean.Macro.throwErrorAt stmt
        "'for' requires a function frame and a typed array parameter"
  | _ => Lean.Macro.throwErrorAt stmt "unsupported RAM statement"

partial def lowerBlock (scope : LocalScope) (strict : Bool) (function : FunctionResolver)
    (body : Array (Lean.TSyntax `ramStmt)) : Lean.MacroM (Lean.TSyntax `term) := do
  if body.isEmpty then return ← `(Ram.Stmt.skip)
  let mut result ← lowerStmt scope strict function body[body.size - 1]!
  for offset in [:body.size - 1] do
    let stmt ← lowerStmt scope strict function body[body.size - 2 - offset]!
    result ← `(Ram.Stmt.seq $stmt $result)
  return result
end

/-- A lowered lexical block and the bindings visible after it. Branch-local
bindings are discarded on exit, but their allocated slots remain in the frame. -/
structure LoweredBlock where
  term : Lean.TSyntax `term
  scope : LocalScope
  immutable : Array Lean.Name
  nextRegister : Nat
  deriving Inhabited

private def checkMutable (immutable : Array Lean.Name) (name : Lean.TSyntax `ident) :
    Lean.MacroM Unit := do
  if immutable.contains name.getId then
    Lean.Macro.throwErrorAt name "cannot assign to an immutable RAM local; use 'let mut'"

/-- Lower lexical declarations with the same expression and statement translator.
Each declaration gets one fresh frame slot; a shadowed binding remains untouched. -/
partial def lowerScopedBlock (scope : LocalScope) (immutable : Array Lean.Name)
    (nextRegister : Nat) (strict : Bool) (function : FunctionResolver)
    (body : Array (Lean.TSyntax `ramStmt)) : Lean.MacroM LoweredBlock := do
  let mut scope := scope
  let mut immutable := immutable
  let mut nextRegister := nextRegister
  let mut statements : Array (Lean.TSyntax `term) := #[]
  for stmt in body do
    let bindLocal (name : Lean.TSyntax `ident) (mutable : Bool)
        (value : Lean.TSyntax `term) := do
      if (arrayField? scope name.getId).isSome then
        Lean.Macro.throwErrorAt name "assign to an array field instead of declaring it with 'let'"
      let register := Lean.Syntax.mkNumLit (toString nextRegister)
      let assignment ← `(Ram.Stmt.assign $register:num $value)
      pure (name, mutable, assignment)
    let bindCall (name : Lean.TSyntax `ident) (mutable : Bool)
        (fn : Lean.TSyntax `ident) (args : Array (Lean.TSyntax `ramExpr)) := do
      if (arrayField? scope name.getId).isSome then
        Lean.Macro.throwErrorAt name "assign to an array field instead of declaring it with 'let'"
      let register := Lean.Syntax.mkNumLit (toString nextRegister)
      let (fn, args) ← function scope strict fn args
      let invocation ← `(Ram.Stmt.call $register:num $fn [$args,*])
      pure (name, mutable, invocation)
    let binding ← match stmt with
      | `(ramStmt| let $name:ident := $value:ramExpr;) =>
          pure (some (← bindLocal name Bool.false (← lowerExpr scope strict value)))
      | `(ramStmt| let mut $name:ident := $value:ramExpr;) =>
          pure (some (← bindLocal name Bool.true (← lowerExpr scope strict value)))
      | `(ramStmt| let $name:ident ← call $fn:ident($args:ramExpr,*);) =>
          pure (some (← bindCall name Bool.false fn args.getElems))
      | `(ramStmt| let mut $name:ident ← call $fn:ident($args:ramExpr,*);) =>
          pure (some (← bindCall name Bool.true fn args.getElems))
      | _ => pure none
    match binding with
    | some (name, mutable, statement) =>
        scope := (scope.filter (fun entry => entry.name != name.getId)).push
          ⟨name.getId, nextRegister, .word⟩
        immutable := immutable.filter (· != name.getId)
        if !mutable then immutable := immutable.push name.getId
        nextRegister := nextRegister + 1
        statements := statements.push statement
    | none =>
        let statement ← match stmt with
          | `(ramStmt| if $condition:ramExpr { $yes:ramStmt* }) => do
              let yes ← lowerScopedBlock scope immutable nextRegister strict function yes
              nextRegister := yes.nextRegister
              `(Ram.Stmt.ite $(← lowerExpr scope strict condition) $(yes.term) Ram.Stmt.skip)
          | `(ramStmt| if $condition:ramExpr { $yes:ramStmt* } else { $no:ramStmt* }) => do
              let yes ← lowerScopedBlock scope immutable nextRegister strict function yes
              let no ← lowerScopedBlock scope immutable yes.nextRegister strict function no
              nextRegister := no.nextRegister
              `(Ram.Stmt.ite $(← lowerExpr scope strict condition) $(yes.term) $(no.term))
          | `(ramStmt| while $condition:ramExpr { $loop:ramStmt* }) => do
              let loop ← lowerScopedBlock scope immutable nextRegister strict function loop
              nextRegister := loop.nextRegister
              `(Ram.Stmt.while $(← lowerExpr scope strict condition) $(loop.term))
          | `(ramStmt| for $element:ident in $array:ident { $loop:ramStmt* }) => do
              let some arrayBinding := scope.find? (fun entry =>
                  entry.name == array.getId && entry.kind == .array)
                | Lean.Macro.throwErrorAt array "expected an array parameter"
              if (arrayField? scope element.getId).isSome then
                Lean.Macro.throwErrorAt element "a loop variable cannot shadow an array field"
              let pointer ← registerTerm nextRegister
              let remaining ← registerTerm (nextRegister + 1)
              let elementRegister := nextRegister + 2
              let elementTerm ← registerTerm elementRegister
              let loopScope := (scope.filter (fun entry => entry.name != element.getId)).push
                ⟨element.getId, elementRegister, .word⟩
              let loopImmutable := (immutable.filter (· != element.getId)).push element.getId
              let loop ← lowerScopedBlock loopScope loopImmutable (nextRegister + 3)
                strict function loop
              nextRegister := loop.nextRegister
              `(Ram.Stmt.forIn $pointer $remaining $elementTerm
                (Ram.Expr.var $(← registerTerm arrayBinding.register))
                (Ram.Expr.var $(← registerTerm (arrayBinding.register + 1))) $(loop.term))
          | _ => do
              match stmt with
              | `(ramStmt| $name:ident := $_value:ramExpr;) => checkMutable immutable name
              | `(ramStmt| $name:ident += $_value:ramExpr;) => checkMutable immutable name
              | `(ramStmt| $name:ident -= $_value:ramExpr;) => checkMutable immutable name
              | `(ramStmt| $name:ident *= $_value:ramExpr;) => checkMutable immutable name
              | `(ramStmt| $name:ident := call $_fn:ident($_args:ramExpr,*);) =>
                  checkMutable immutable name
              | `(ramStmt| read $name:ident;) => checkMutable immutable name
              | _ => pure ()
              lowerStmt scope strict function stmt
        statements := statements.push statement
  let term ← if statements.isEmpty then `(Ram.Stmt.skip) else do
    let mut term := statements[statements.size - 1]!
    for offset in [:statements.size - 1] do
      term ← `(Ram.Stmt.seq $(statements[statements.size - 2 - offset]!) $term)
    pure term
  return ⟨term, scope, immutable, nextRegister⟩

/-- The function term and source bindings produced by one lowering. -/
structure LoweredFunction where
  term : Lean.TSyntax `term
  scope : LocalScope
  registers : Nat

/-- Lower a function and retain its lexical bindings for generated proof names. -/
def lowerFunctionWithScope (strict : Bool) (function : FunctionResolver)
    (params : Array Parameter) (localNames : Array (Lean.TSyntax `ident))
    (body : Array (Lean.TSyntax `ramStmt))
    (result : Lean.TSyntax `ramExpr) : Lean.MacroM LoweredFunction := do
  let parameterScope ← makeParameterScope params
  let scope ← makeParameterScope (params ++ localNames.map (fun name => ⟨name, .word⟩))
  let body ← lowerScopedBlock scope #[] (localRegisterCount scope) strict function body
  let paramCount := Lean.Syntax.mkNumLit (toString (localRegisterCount parameterScope))
  let localCount := Lean.Syntax.mkNumLit (toString body.nextRegister)
  let term ← `(Ram.Func.mk $paramCount $localCount $(body.term)
    $(← lowerExpr body.scope strict result))
  return ⟨term, body.scope, body.nextRegister⟩

def lowerFunction (strict : Bool) (function : FunctionResolver)
    (params localNames : Array (Lean.TSyntax `ident))
    (localsKeyword : Lean.TSyntax `ident) (body : Array (Lean.TSyntax `ramStmt))
    (result : Lean.TSyntax `ramExpr) : Lean.MacroM (Lean.TSyntax `term) := do
  if localsKeyword.getId != `locals then
    Lean.Macro.throwErrorAt localsKeyword "expected 'locals' followed by local register names"
  return (← lowerFunctionWithScope strict function (params.map fun name => ⟨name, .word⟩)
    localNames body result).term

macro_rules
  | `(ram_expr% $expr:ramExpr) => do return ← lowerExpr #[] Bool.false expr
  | `(ram_stmt% $stmt:ramStmt) => do return ← lowerStmt #[] Bool.false externalFunction stmt
  | `(ram% { $body:ramStmt* }) => do return ← lowerBlock #[] Bool.false externalFunction body

/-- Declare function-local register names without hand-numbering them.
Parameters occupy the initial registers, followed by the declared locals.
The final return expression is exactly the existing `Func.result`. -/
syntax:max "ram_fun% " "(" ident,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : term

/-- Function locals may instead be introduced where used with `let` or `let mut`. -/
syntax:max "ram_fun% " "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : term

macro_rules
  | `(ram_fun% ($params:ident,*) $localsKeyword:ident ($localNames:ident,*) {
      $body:ramStmt* return $result:ramExpr; }) => do
      return ← lowerFunction Bool.false externalFunction params.getElems localNames.getElems
        localsKeyword body result
  | `(ram_fun% ($params:ident,*) { $body:ramStmt* return $result:ramExpr; }) => do
      return (← lowerFunctionWithScope Bool.true externalFunction
        (params.getElems.map fun name => ⟨name, .word⟩) #[]
        body result).term

/-!
### Examples

See `Examples.Ram.Syntax` for source programs and their definitional expansions.
The resulting functions use the same compiler and correctness judgments as
handwritten syntax trees.
-/

end Ram.DSL
