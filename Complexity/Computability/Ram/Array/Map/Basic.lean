/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.ForIn
import Complexity.Computability.Ram.Verification.Function
import Complexity.Computability.Ram.Source.Frame

/-!
# In-place mapping through a statically linked function

The source operation takes a borrowed array in its first two parameter slots.
It keeps an index, uses the ordinary `forIn` load and cursor updates,
and calls the fixed source function `fn` before storing each returned word.
The remaining slots are private locals, exactly as in the named DSL declaration
with `for i, x in xs { let y ← call helper(x); xs[i] := y; }`.

The mathematical transformation below describes a verified callee; it is not
an executable Lean callback or a second interpretation of the program.
-/

namespace Ram.Source.Array.Map

/-- One actual helper call, indexed store and explicit index increment.
The iteration mechanism supplies the element in local 5. -/
def body (fn : Nat) : Stmt :=
  .seq (.call [6] fn [.var 5])
    (.seq (.store (.bin .add (.var 0) (.var 2)) (.var 6))
      (.assign 2 (.bin .add (.var 2) (.const 1))))

/-- Initialize the public source index and traverse the borrowed array. -/
def code (fn : Nat) : Stmt :=
  .seq (.assign 2 (.const 0))
    (Stmt.forIn 3 4 5 (.var 0) (.var 1) (body fn))

/-- The ordinary source function underlying the reusable map operation.
Its helper index is resolved statically, not passed in a runtime word. -/
def function (fn : Nat) : Func :=
  { params := 2, locals := 7, body := code fn, results := [] }

/-- The shared effects and local assignments of the body after loading an element. -/
def bodyState (transform : Word w → Word w) (s : State w) : State w :=
  ((s.setReg 6 (transform (s.regs 5))).setMem
    (s.regs 0 + s.regs 2) (transform (s.regs 5))).setReg 2 (s.regs 2 + 1)

/-- A callee contract at the actual loaded word suffices for the body.
The callee preserves shared state; the subsequent real store changes the array. -/
theorem body_safe_at {program : Program} {helper : Func} {fn heapLimit depth : Nat}
    {transform : Word w → Word w} (lookup : program[fn]? = some helper) (s : State w)
    (correct : FunctionContract program heapLimit depth helper
      (fun args _ => args = [s.regs 5])
      (fun _ entry value finish => value = [transform (s.regs 5)] ∧ finish = entry))
    (address : (s.regs 0 + s.regs 2).toNat < heapLimit) :
    SafeExec program heapLimit (depth + 1) (body fn) s (bodyState transform s) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ := correct [s.regs 5] s rfl
  have resultCount : [6].length = helper.results.length := by
    simpa only [List.length_cons, List.length_nil] using execution.length_eq
  have call := execution.call (dsts := [6]) (exprs := [.var 5]) lookup resultCount
    (by simp [Expr.ReadsBelow])
  refine .seq call (.seq (.store ⟨trivial, trivial⟩ trivial ?_) (.assign ⟨trivial, trivial⟩))
  simpa [State.setReg, State.eval, Expr.eval, BinOp.eval] using address

/-- Completed bodies preserve the private remaining count independently of
the helper's behavior: the actual call restores caller locals before binding its result. -/
theorem body_remaining {program : Program} {fn heapLimit depth : Nat} {s t : State w}
    (execution : SafeExec program heapLimit depth (body fn) s t) :
    t.regs 4 = s.regs 4 := by
  exact execution.regs_eq_of_not_mem_writtenRegs (by simp [body, Stmt.writtenRegs])

end Ram.Source.Array.Map
