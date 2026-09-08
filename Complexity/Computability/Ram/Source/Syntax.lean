/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic
import Lean

/-!
# A surface language for the verified RAM AST

`ram_expr%` quotes an expression, `ram% { ... }` quotes a statement block, and
`ram_fun% (parameters) locals (locals) { ... return expression; }` quotes a
function. Function syntax assigns successive local register numbers only at
variable occurrences, not by introducing Lean bindings around the body.
Outside that syntax, identifiers refer to ordinary Lean bindings of type
`Ram.Reg`; legacy call targets refer to Lean `Nat` bindings. Function targets
and `const(t)` retain their enclosing Lean scope, even when a parameter has
the same spelling. `Complexity.Computability.Ram.Source.Named.Basic` adds a separately resolved named function table.

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
syntax "if " ramExpr " {" ramStmt* "}" : ramStmt
syntax "if " ramExpr " {" ramStmt* "}" " else " "{" ramStmt* "}" : ramStmt
syntax "while " ramExpr " {" ramStmt* "}" : ramStmt

/-- Quote a RAM statement block. Braces delimit control-flow bodies; atomic
statements end in semicolons. Empty blocks are `Stmt.skip`. -/
syntax:max "ram% " "{" ramStmt* "}" : term

/-- Quote a single surface statement. Usually used through `ram% { ... }`. -/
syntax:max "ram_stmt% " ramStmt : term

/- The bound-variable translator deliberately visits only RAM variable
positions. In particular it never rewrites a call target or the Lean term
inside `const(...)`. This keeps the three namespaces independent. -/

abbrev LocalScope := Array (Lean.Name × Nat)
abbrev FunctionResolver := Lean.TSyntax `ident → Lean.MacroM (Lean.TSyntax `term)

def makeLocalScope (names : Array (Lean.TSyntax `ident)) : Lean.MacroM LocalScope := do
  let mut scope := #[]
  for name in names do
    if scope.any (fun entry => entry.1 == name.getId) then
      Lean.Macro.throwErrorAt name "duplicate RAM parameter or local name"
    scope := scope.push (name.getId, scope.size)
  return scope

def resolveLocal (scope : LocalScope) (strict : Bool) (name : Lean.TSyntax `ident) :
    Lean.MacroM (Lean.TSyntax `term) := do
  match scope.find? (fun entry => entry.1 == name.getId) with
  | some (_, index) =>
      let index := Lean.Syntax.mkNumLit (toString index)
      `($index:num)
  | none =>
      if strict then
        Lean.Macro.throwErrorAt name "unknown RAM local variable"
      else
        `($name:ident)

def externalFunction : FunctionResolver := fun name => `($name:ident)

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
      `(Ram.Stmt.store (Ram.Expr.bin .add (Ram.Expr.var $(← resolveVar a)) $(← expr i)) $(← expr e))
  | `(ramStmt| store[$a:ramExpr] := $e:ramExpr;) => `(Ram.Stmt.store $(← expr a) $(← expr e))
  | `(ramStmt| read $x:ident;) => `(Ram.Stmt.read $(← resolveVar x))
  | `(ramStmt| write $e:ramExpr;) => `(Ram.Stmt.write $(← expr e))
  | `(ramStmt| $x:ident := call $f:ident($args:ramExpr,*);) =>
      let es ← args.getElems.mapM expr
      `(Ram.Stmt.call $(← resolveVar x) $(← function f) [$es,*])
  | `(ramStmt| if $c:ramExpr { $yes:ramStmt* }) =>
      `(Ram.Stmt.ite $(← expr c) $(← block yes) Ram.Stmt.skip)
  | `(ramStmt| if $c:ramExpr { $yes:ramStmt* } else { $no:ramStmt* }) =>
      `(Ram.Stmt.ite $(← expr c) $(← block yes) $(← block no))
  | `(ramStmt| while $c:ramExpr { $body:ramStmt* }) =>
      `(Ram.Stmt.while $(← expr c) $(← block body))
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

def lowerFunction (strict : Bool) (function : FunctionResolver)
    (params localNames : Array (Lean.TSyntax `ident))
    (localsKeyword : Lean.TSyntax `ident) (body : Array (Lean.TSyntax `ramStmt))
    (result : Lean.TSyntax `ramExpr) : Lean.MacroM (Lean.TSyntax `term) := do
  if localsKeyword.getId != `locals then
    Lean.Macro.throwErrorAt localsKeyword "expected 'locals' followed by local register names"
  let scope ← makeLocalScope (params ++ localNames)
  let paramCount := Lean.Syntax.mkNumLit (toString params.size)
  let localCount := Lean.Syntax.mkNumLit (toString scope.size)
  `(Ram.Func.mk $paramCount $localCount
    $(← lowerBlock scope strict function body) $(← lowerExpr scope strict result))

macro_rules
  | `(ram_expr% $expr:ramExpr) => do return ← lowerExpr #[] Bool.false expr
  | `(ram_stmt% $stmt:ramStmt) => do return ← lowerStmt #[] Bool.false externalFunction stmt
  | `(ram% { $body:ramStmt* }) => do return ← lowerBlock #[] Bool.false externalFunction body

/-- Declare function-local register names without hand-numbering them.
Parameters occupy the initial registers, followed by the declared locals.
The final return expression is exactly the existing `Func.result`. -/
syntax:max "ram_fun% " "(" ident,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : term

macro_rules
  | `(ram_fun% ($params:ident,*) $localsKeyword:ident ($localNames:ident,*) {
      $body:ramStmt* return $result:ramExpr; }) => do
      return ← lowerFunction Bool.false externalFunction params.getElems localNames.getElems
        localsKeyword body result

/-!
### Examples

See `Examples.Ram.Syntax` for source programs and their definitional expansions.
The resulting functions use the same compiler and correctness judgments as
handwritten syntax trees.
-/

end Ram.DSL
