import Ram.Source
import Lean

/-!
# A surface language for the verified RAM AST

`ram_expr%` quotes an expression, `ram% { ... }` quotes a statement block, and
`ram_fun% (parameters) locals (locals) { ... return expression; }` quotes a
function. Function syntax assigns successive local register numbers to the
parameter and local names. Outside that syntax, identifiers refer to ordinary
Lean bindings of type `Ram.Reg`; call targets refer to Lean `Nat` bindings.

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

macro_rules
  | `(ram_expr% $n:num) => `(Ram.Expr.const $n)
  | `(ram_expr% $x:ident) => `(Ram.Expr.var $x)
  | `(ram_expr% ($e:ramExpr)) => `(ram_expr% $e)
  | `(ram_expr% const($n:term)) => `(Ram.Expr.const $n)
  | `(ram_expr% load[$a:ramExpr]) => `(Ram.Expr.load (ram_expr% $a))
  | `(ram_expr% true) => `(Ram.Expr.const 1)
  | `(ram_expr% false) => `(Ram.Expr.const 0)
  | `(ram_expr% $a:ramExpr[$i:ramExpr]) => `(Ram.Expr.index (ram_expr% $a) (ram_expr% $i))
  | `(ram_expr% !$e:ramExpr) => `(Ram.Expr.bin .eq (ram_expr% $e) (Ram.Expr.const 0))
  | `(ram_expr% -$e:ramExpr) => `(Ram.Expr.bin .sub (Ram.Expr.const 0) (ram_expr% $e))
  | `(ram_expr% $a:ramExpr + $b:ramExpr) => `(Ram.Expr.bin .add (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr - $b:ramExpr) => `(Ram.Expr.bin .sub (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr * $b:ramExpr) => `(Ram.Expr.bin .mul (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr / $b:ramExpr) => `(Ram.Expr.bin .udiv (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr % $b:ramExpr) => `(Ram.Expr.bin .umod (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr << $b:ramExpr) => `(Ram.Expr.bin .shl (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr >> $b:ramExpr) => `(Ram.Expr.bin .shr (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr &&& $b:ramExpr) => `(Ram.Expr.bin .band (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr ^^^ $b:ramExpr) => `(Ram.Expr.bin .bxor (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr ||| $b:ramExpr) => `(Ram.Expr.bin .bor (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr == $b:ramExpr) => `(Ram.Expr.bin .eq (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr != $b:ramExpr) =>
      `(Ram.Expr.bin .eq (Ram.Expr.bin .eq (ram_expr% $a) (ram_expr% $b)) (Ram.Expr.const 0))
  | `(ram_expr% $a:ramExpr < $b:ramExpr) => `(Ram.Expr.bin .ult (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr <= $b:ramExpr) => `(Ram.Expr.bin .ule (ram_expr% $a) (ram_expr% $b))
  | `(ram_expr% $a:ramExpr > $b:ramExpr) => `(Ram.Expr.bin .ult (ram_expr% $b) (ram_expr% $a))
  | `(ram_expr% $a:ramExpr >= $b:ramExpr) => `(Ram.Expr.bin .ule (ram_expr% $b) (ram_expr% $a))

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

macro_rules
  | `(ram% {}) => `(Ram.Stmt.skip)
  | `(ram% { $s:ramStmt }) => `(ram_stmt% $s)
  | `(ram% { $s:ramStmt $ss:ramStmt* }) => `(Ram.Stmt.seq (ram_stmt% $s) (ram% { $ss* }))

macro_rules
  | `(ram_stmt% skip;) => `(Ram.Stmt.skip)
  | `(ram_stmt% $x:ident := $e:ramExpr;) => `(Ram.Stmt.assign $x (ram_expr% $e))
  | `(ram_stmt% $x:ident += $e:ramExpr;) =>
      `(Ram.Stmt.assign $x (Ram.Expr.bin .add (Ram.Expr.var $x) (ram_expr% $e)))
  | `(ram_stmt% $x:ident -= $e:ramExpr;) =>
      `(Ram.Stmt.assign $x (Ram.Expr.bin .sub (Ram.Expr.var $x) (ram_expr% $e)))
  | `(ram_stmt% $x:ident *= $e:ramExpr;) =>
      `(Ram.Stmt.assign $x (Ram.Expr.bin .mul (Ram.Expr.var $x) (ram_expr% $e)))
  | `(ram_stmt% $a:ident[$i:ramExpr] := $e:ramExpr;) =>
      `(Ram.Stmt.store (Ram.Expr.bin .add (Ram.Expr.var $a) (ram_expr% $i)) (ram_expr% $e))
  | `(ram_stmt% store[$a:ramExpr] := $e:ramExpr;) =>
      `(Ram.Stmt.store (ram_expr% $a) (ram_expr% $e))
  | `(ram_stmt% read $x:ident;) => `(Ram.Stmt.read $x)
  | `(ram_stmt% write $e:ramExpr;) => `(Ram.Stmt.write (ram_expr% $e))
  | `(ram_stmt% $x:ident := call $f:ident($args:ramExpr,*);) => do
      let es ← args.getElems.mapM fun e => `(ram_expr% $e)
      `(Ram.Stmt.call $x $f [$es,*])
  | `(ram_stmt% if $c:ramExpr { $yes:ramStmt* }) =>
      `(Ram.Stmt.ite (ram_expr% $c) (ram% { $yes* }) Ram.Stmt.skip)
  | `(ram_stmt% if $c:ramExpr { $yes:ramStmt* } else { $no:ramStmt* }) =>
      `(Ram.Stmt.ite (ram_expr% $c) (ram% { $yes* }) (ram% { $no* }))
  | `(ram_stmt% while $c:ramExpr { $body:ramStmt* }) =>
      `(Ram.Stmt.while (ram_expr% $c) (ram% { $body* }))

/-- Declare function-local register names without hand-numbering them.
Parameters occupy the initial registers, followed by the declared locals.
The final return expression is exactly the existing `Func.result`. -/
syntax:max "ram_fun% " "(" ident,* ")" ident "(" ident,* ")" "{"
  ramStmt* "return " ramExpr ";" "}" : term

macro_rules
  | `(ram_fun% ($params:ident,*) $localsKeyword:ident ($localNames:ident,*) {
      $body:ramStmt* return $result:ramExpr; }) => do
      if localsKeyword.getId != `locals then
        Lean.Macro.throwErrorAt localsKeyword "expected 'locals' followed by local register names"
      let names := params.getElems ++ localNames.getElems
      let mut seen : List Lean.Name := []
      for name in names do
        if seen.contains name.getId then
          Lean.Macro.throwErrorAt name "duplicate RAM parameter or local name"
        seen := name.getId :: seen
      let paramCount := Lean.Syntax.mkNumLit (toString params.getElems.size)
      let localCount := Lean.Syntax.mkNumLit (toString names.size)
      let mut term ← `(Ram.Func.mk $paramCount $localCount (ram% { $body* }) (ram_expr% $result))
      for offset in [:names.size] do
        let i := names.size - 1 - offset
        let name := names[i]!
        let index := Lean.Syntax.mkNumLit (toString i)
        term ← `(let $name:ident : Ram.Reg := $index; $term)
      return term

/-!
## Executable language examples and their AST meaning

The equalities below are definitional expansion lemmas, not a second semantics
or a testing framework. These functions can be supplied directly to the
existing compiler and correctness judgments.
-/

namespace Examples

/-- Scale an array in place and accumulate its new elements. Word arithmetic
wraps as usual; an exact-integer specification additionally needs range proofs. -/
def scaleAndSum : Func :=
  ram_fun% (base, size, factor) locals (i, total) {
    i := 0;
    total := 0;
    while i < size {
      base[i] := base[i] * factor;
      total += base[i];
      i += 1;
    }
    return total;
  }

theorem scaleAndSum_expands : scaleAndSum =
    { params := 3
      locals := 5
      body := .seq (.assign 3 (.const 0))
        (.seq (.assign 4 (.const 0))
          (.while (.bin .ult (.var 3) (.var 1))
            (.seq (.store (.bin .add (.var 0) (.var 3))
                (.bin .mul (.load (.bin .add (.var 0) (.var 3))) (.var 2)))
              (.seq (.assign 4 (.bin .add (.var 4) (.load (.bin .add (.var 0) (.var 3)))))
                (.assign 3 (.bin .add (.var 3) (.const 1)))))))
      result := .var 4 } := rfl

/-- A static function-table name. Putting `euclid` at index zero makes the
call below recursive; the syntax does not inline it or assume it terminates. -/
def euclidId : Nat := 0

def euclid : Func :=
  ram_fun% (a, b) locals (answer) {
    if b == 0 {
      answer := a;
    } else {
      answer := call euclidId(b, a % b);
    }
    return answer;
  }

theorem euclid_expands : euclid =
    { params := 2
      locals := 3
      body := .ite (.bin .eq (.var 1) (.const 0)) (.assign 2 (.var 0))
        (.call 2 euclidId [.var 1, .bin .umod (.var 0) (.var 1)])
      result := .var 2 } := rfl

/-- Direct statement syntax also accepts caller-provided Lean register names. -/
def readStoreWrite (base value : Reg) : Stmt := ram% {
  read value;
  store[base + 2] := value;
  write load[base + 2];
}

theorem readStoreWrite_expands (base value : Reg) : readStoreWrite base value =
    .seq (.read value)
      (.seq (.store (.bin .add (.var base) (.const 2)) (.var value))
        (.write (.load (.bin .add (.var base) (.const 2))))) := rfl

end Examples
end Ram.DSL
