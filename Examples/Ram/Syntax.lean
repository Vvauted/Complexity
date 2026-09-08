/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Syntax

/-!
# Structured RAM syntax examples
-/

namespace Ram.DSL

namespace Examples

/-- Scale an array in place and accumulate its new elements. Word arithmetic
wraps as usual; an exact-integer specification additionally needs range proofs. -/
def scaleAndSum : Func :=
  ram_fun% (base, size, factor) {
    let mut i := 0;
    let mut total := 0;
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
      results := [.var 4] } := rfl

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
        (.call [2] euclidId [.var 1, .bin .umod (.var 0) (.var 1)])
      results := [.var 2] } := rfl

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

/-- A local may share a spelling with a host constant or legacy function label.
Only variable positions use its register number. -/
def outerTarget : Nat := 3

def separateScopes : Func := ram_fun% (outerTarget) locals (answer) {
  answer := call outerTarget(outerTarget);
  return const(outerTarget);
}

theorem separateScopes_expands : separateScopes =
    { params := 1, locals := 2
      body := .call [1] 3 [.var 0]
      results := [.const 3] } := rfl

end Examples
end Ram.DSL
