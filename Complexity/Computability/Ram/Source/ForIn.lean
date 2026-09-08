/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic

/-!
# Array iteration through ordinary source instructions

`Ram.Stmt.forIn` copies a base address and length into cursor locals, then
loads one element before each execution of its body. It is a constructor for
the existing statement AST, not a new instruction or an uncharged bulk operation.

The source frontend reserves fresh cursor and element locals. The helper itself
does not impose freshness: verification rules must account for the actual
registers and expression evaluation order. In particular, length is evaluated
after assigning the pointer. Array contents are read at each iteration, not
copied into a snapshot before the loop.
-/

namespace Ram.Stmt

/-- One iteration: load the current element, run the body, and advance the cursor. -/
def forInBody (pointer remaining element : Reg) (body : Stmt) : Stmt :=
  .seq (.assign element (.load (.var pointer)))
    (.seq body
      (.seq (.assign pointer (.bin .add (.var pointer) (.const 1)))
        (.assign remaining (.bin .sub (.var remaining) (.const 1)))))

/-- Iterate with an already initialized pointer and remaining count. -/
def forInLoop (pointer remaining element : Reg) (body : Stmt) : Stmt :=
  .while (.var remaining) (forInBody pointer remaining element body)

/-- Traverse consecutive words using cursor locals. The length is
copied once; every iteration performs one load, the body, a pointer increment
and a remaining-count decrement. Setup evaluates the base before the length. -/
def forIn (pointer remaining element : Reg) (base length : Expr) (body : Stmt) : Stmt :=
  .seq (.assign pointer base)
    (.seq (.assign remaining length)
      (forInLoop pointer remaining element body))

end Ram.Stmt
