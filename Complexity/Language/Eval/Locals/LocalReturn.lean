/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Composition

/-!
# Source fragments for an inline local return

`LocalReturn.store` records a value in an existing optional local and clears an
existing Boolean. `LocalReturn.resume` runs a continuation only while that
Boolean is set. Both are combinations of ordinary source statements, with their
actual local updates, heap and execution costs; neither catches a function
return or defines another evaluator. Loop guards and increments can use the
corresponding fragments in `RangeControl`.

The root lemmas compare a pending local result with the same value carried by
`Control.returned`. A fault is compared only with an empty pending slot: a fault
does not carry a return root. A pending value left over after a failed scratch
exit cannot simply be ignored when checking an enclosing scratch scope.

Consequently, each scratch scope needs its own temporary result and flag,
lexically inside its parent scope but outside its own body. The body writes
those slots, and only a successful normal scope exit commits them to the parent
slots. On a fault, sequencing skips the commit and lexical scope exit drops the
temporary slots before the parent scratch check. The lemmas here supply the
local root comparison, not a proof of that complete lowering or a permission to
discard roots only in a proof view.
-/

namespace Complexity.Language.Stmt.LocalReturn

variable {signatures : List Signature} {Γ : List Ty} {result τ : Ty} {Locals : Type}

/-- Save the actual atomic result, then stop this local continuation. These are
two ordinary assignments; the surrounding statement still completes normally. -/
def store (pending : Var Γ (.option τ)) (live : Var Γ .bool)
    (value : Atom Γ τ) : Stmt signatures Γ result :=
  .seq (.assign pending (.some value)) (.assign live (.atom (.bool false)))

/-- Run the actual continuation only while the local block is still active.
The stopped branch does not evaluate that continuation at all. -/
def resume (live : Atom Γ .bool) (next : Stmt signatures Γ result) :
    Stmt signatures Γ result :=
  .ite live next .skip

/-- Storing a local result evaluates its atom in the original locals, updates
only the two selected bindings and leaves the actual heap unchanged. -/
theorem observe_store (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Var Γ (.option τ)) (live : Var Γ .bool) (value : Atom Γ τ)
    (locals : Locals) :
    observe view (store pending live value : Stmt signatures Γ result) program locals =
      pure (.normal, view
        (((view.symm locals).set pending (some (value.eval (view.symm locals)))).set live false)) := by
  simp only [store, observe_seq, observe_assign, Prim.eval, Atom.eval, pure_bind,
    Equiv.symm_apply_apply]

/-- An active block runs exactly its supplied continuation, including its
heap effects, returns, faults or divergence. -/
theorem observe_resume_true (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (next : Stmt signatures Γ result) (locals : Locals)
    (running : live.eval (view.symm locals) = true) :
    observe view (resume live next) program locals = observe view next program locals := by
  rw [resume, observe_ite, running, if_pos rfl]

/-- A completed local block skips the continuation without any premise about
that continuation's effects, successful execution or termination. -/
theorem observe_resume_false (view : Env Γ ≃ Locals) (program : Program signatures)
    (live : Atom Γ .bool) (next : Stmt signatures Γ result) (locals : Locals)
    (stopped : live.eval (view.symm locals) = false) :
    observe view (resume live next) program locals = pure (.normal, locals) := by
  rw [resume, observe_ite, stopped]
  simp only [Bool.false_eq_true, if_false, observe_skip]

/-- A Boolean and an empty result slot add no retained roots on a normal exit.
The statement result types on the two sides need not coincide. -/
theorem scopeSafe_none (initial : Heap) (finish : State Γ) (live : Bool) :
    ScopeSafe initial
      (State.cons (τ := .bool) live (State.cons (τ := .option τ) none finish))
      (.normal : Control result) ↔
    ScopeSafe initial finish (.normal : Control τ) := by
  simp [ScopeSafe, State.cons]

/-- A pending result retained as a local has exactly the roots of the same
returned value. This equivalence includes unsafe results; it assumes neither
valid contents nor successful scratch cleanup. -/
theorem scopeSafe_some (initial : Heap) (finish : State Γ) (live : Bool)
    (value : Value τ) :
    ScopeSafe initial
      (State.cons (τ := .bool) live (State.cons (τ := .option τ) (some value) finish))
      (.normal : Control result) ↔
    ScopeSafe initial finish (.returned value : Control τ) := by
  simp [ScopeSafe, State.cons, and_comm]

/-- A fault adds no return root. This comparison requires the pending slot to
be empty; a nonempty slot can change an enclosing scope's cleanup decision even
though the fault itself is unchanged. -/
theorem scopeSafe_fault (initial : Heap) (finish : State Γ) (live : Bool) (error : Fault) :
    ScopeSafe initial
      (State.cons (τ := .bool) live (State.cons (τ := .option τ) none finish))
      (.fault error : Control result) ↔
    ScopeSafe initial finish (.fault error : Control τ) := by
  simp [ScopeSafe, State.cons]

end Complexity.Language.Stmt.LocalReturn
