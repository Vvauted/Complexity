/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals.Composition

/-!
# Source fragments for an inline local return

`LocalReturn.store` records a value in an existing optional local.
`LocalReturn.resume` runs a continuation only while that local is empty, and
`LocalReturn.guard` skips the original loop guard once a result is stored. These
are combinations of ordinary source statements, with their actual local
updates, heap and execution costs; they neither catch a function return nor
define another evaluator. Their `some` branches retain the ordinary option
match's real lexical payload binding.

The root lemmas retain the pending slot's roots separately from the actual
control, or compare a pending local result with the same returned value. A fault
does not itself carry a return root. A pending value left over after a failed
scratch exit cannot simply be ignored when checking an enclosing scratch scope;
an optional Unit result is root-free even in this case.

Consequently, each scratch scope needs its own temporary result,
lexically inside its parent scope but outside its own body. The body writes
this slot, and only a successful normal scope exit commits it to the parent
slot. On a fault, sequencing skips the commit and lexical scope exit drops the
temporary slot before the parent scratch check. The lemmas here supply the
local root comparison, not a proof of that complete lowering or a permission to
discard roots only in a proof view.
-/

namespace Complexity.Language.Stmt.LocalReturn

variable {signatures : List Signature} {Γ : List Ty} {result τ : Ty} {Locals : Type}

/-- Save the actual atomic result in the local completion slot. This is one
ordinary assignment; the surrounding statement still completes normally. -/
def store (pending : Var Γ (.option τ)) (value : Atom Γ τ) : Stmt signatures Γ result :=
  .assign pending (.some value)

/-- Run the actual continuation only while no local result has been stored.
The completed branch binds and drops the real option payload without running
the continuation. -/
def resume (pending : Atom Γ (.option τ)) (next : Stmt signatures Γ result) :
    Stmt signatures Γ result :=
  .matchOption pending next .skip

/-- Evaluate the original guard only while the local block is incomplete.
A stored result takes the real payload-binding branch and returns false. -/
def guard (pending : Atom Γ (.option τ)) (test : Stmt signatures Γ .bool) :
    Stmt signatures Γ .bool :=
  .matchOption pending test (.ret (.bool false))

/-- Storing a local result evaluates its atom in the original locals, updates
only the selected binding and leaves the actual heap unchanged. -/
theorem observe_store (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Var Γ (.option τ)) (value : Atom Γ τ)
    (locals : Locals) :
    observe view (store pending value : Stmt signatures Γ result) program locals =
      pure (.normal, view ((view.symm locals).set pending
        (some (value.eval (view.symm locals))))) := by
  simp only [store, observe_assign, Prim.eval]

/-- An active block runs exactly its supplied continuation, including its
heap effects, returns, faults or divergence. -/
theorem observe_resume_none (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Atom Γ (.option τ)) (next : Stmt signatures Γ result) (locals : Locals)
    (running : pending.eval (view.symm locals) = none) :
    observe view (resume pending next) program locals = observe view next program locals := by
  rw [resume, observe_matchOption, running]

/-- A completed local block skips the continuation without any premise about
that continuation's effects, successful execution or termination. -/
theorem observe_resume_some (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Atom Γ (.option τ)) (next : Stmt signatures Γ result) (locals : Locals)
    (value : Value τ) (stopped : pending.eval (view.symm locals) = some value) :
    observe view (resume pending next) program locals = pure (.normal, locals) := by
  rw [resume, observe_matchOption, stopped]
  simp only [observe_skip, pure_bind]

/-- An empty local result slot evaluates the actual loop guard, with all of
that guard's heap effects, control outcomes and possible divergence. -/
theorem observe_guard_none (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Atom Γ (.option τ)) (test : Stmt signatures Γ .bool) (locals : Locals)
    (running : pending.eval (view.symm locals) = none) :
    observe view (guard pending test) program locals = observe view test program locals := by
  rw [guard, observe_matchOption, running]

/-- A stored local result bypasses the original guard and returns false,
retaining the current outer locals and actual heap. -/
theorem observe_guard_some (view : Env Γ ≃ Locals) (program : Program signatures)
    (pending : Atom Γ (.option τ)) (test : Stmt signatures Γ .bool) (locals : Locals)
    (value : Value τ) (stopped : pending.eval (view.symm locals) = some value) :
    observe view (guard pending test) program locals = pure (.returned false, locals) := by
  rw [guard, observe_matchOption, stopped]
  simp only [observe_ret, Atom.eval, pure_bind]

/-- Separate the roots of a pending local result from the unchanged actual
control. In particular, a fault does not erase a nonempty slot's roots. -/
theorem scopeSafe_pending (initial : Heap) (finish : State Γ)
    (pending : Option (Value τ)) (control : Control result) :
    ScopeSafe initial (State.cons (τ := .option τ) pending finish) control ↔
    ValueRooted initial (τ := .option τ) pending ∧ ScopeSafe initial finish control := by
  simp [ScopeSafe, State.cons, and_assoc]

/-- An optional Unit result adds no roots, for every actual
control, including faults with a nonempty pending slot. -/
theorem scopeSafe_unit (initial : Heap) (finish : State Γ)
    (pending : Option Unit) (control : Control result) :
    ScopeSafe initial (State.cons (τ := .option .unit) pending finish) control ↔
      ScopeSafe initial finish control := by
  rw [scopeSafe_pending (τ := .unit)]
  cases pending <;> simp

/-- An empty result slot adds no retained roots on a normal exit.
The statement result types on the two sides need not coincide. -/
theorem scopeSafe_none (initial : Heap) (finish : State Γ) :
    ScopeSafe initial (State.cons (τ := .option τ) none finish)
      (.normal : Control result) ↔
    ScopeSafe initial finish (.normal : Control τ) := by
  simp [ScopeSafe, State.cons]

/-- A pending result retained as a local has exactly the roots of the same
returned value. This equivalence includes unsafe results; it assumes neither
valid contents nor successful scratch cleanup. -/
theorem scopeSafe_some (initial : Heap) (finish : State Γ)
    (value : Value τ) :
    ScopeSafe initial (State.cons (τ := .option τ) (some value) finish)
      (.normal : Control result) ↔
    ScopeSafe initial finish (.returned value : Control τ) := by
  simp [ScopeSafe, State.cons, and_comm]

/-- A fault adds no return root. This comparison requires the pending slot to
be empty; a nonempty slot can change an enclosing scope's cleanup decision even
though the fault itself is unchanged. -/
theorem scopeSafe_fault (initial : Heap) (finish : State Γ) (error : Fault) :
    ScopeSafe initial (State.cons (τ := .option τ) none finish)
      (.fault error : Control result) ↔
    ScopeSafe initial finish (.fault error : Control τ) := by
  simp [ScopeSafe, State.cons]

end Complexity.Language.Stmt.LocalReturn
