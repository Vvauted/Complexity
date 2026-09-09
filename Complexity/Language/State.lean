/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Heap

/-!
# Typed source locals and shared state

Local updates change one typed lexical variable. Entering a call installs the
actual arguments while retaining the shared heap; returning restores only the
caller locals and retains the callee's actual final heap. Leaving a lexical
scope likewise drops only its innermost binding, not any heap effects or changes
to outer locals.

These operations prepare the state interface for the source semantics. They do
not define a second execution relation, introduce a monad or enable additional
statement forms by themselves.
-/

namespace Complexity.Language

namespace Env

/-- Replace one typed lexical value, retaining every other binding. -/
def set : {Γ : List Ty} → {τ : Ty} → Env Γ → Var Γ τ → Value τ → Env Γ
  | _, _, env, .here, value => cons value env.tail
  | _, _, env, .there v, value => cons env.head (set env.tail v value)

/-- Updating the innermost binding retains the outer environment. -/
@[simp] theorem set_here {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ)) (value : Value τ) :
    env.set .here value = cons value env.tail := rfl

/-- Updating an outer binding retains the actual innermost value. -/
@[simp] theorem set_there {Γ : List Ty} {τ σ : Ty} (env : Env (σ :: Γ))
    (v : Var Γ τ) (value : Value τ) :
    env.set (.there v) value = cons env.head (env.tail.set v value) := rfl

/-- The updated variable contains exactly the new mathematical value. -/
@[simp] theorem get_set_self {Γ : List Ty} {τ : Ty} (env : Env Γ)
    (v : Var Γ τ) (value : Value τ) :
    (env.set v value).get v = value := by
  induction v with
  | here => rfl
  | there v ih => exact ih env.tail value

private theorem get_set_of_ne_same {Γ : List Ty} {τ : Ty} (env : Env Γ)
    (v : Var Γ τ) (value : Value τ) (other : Var Γ τ) (different : v ≠ other) :
    (env.set v value).get other = env.get other := by
  induction v with
  | here =>
      cases other with
      | here => exact False.elim (different rfl)
      | there other => rfl
  | there v ih =>
      cases other with
      | here => rfl
      | there other =>
          exact ih env.tail value other (fun same => different (congrArg Var.there same))

private theorem get_set_of_type_ne {Γ : List Ty} {τ σ : Ty} (env : Env Γ)
    (v : Var Γ τ) (value : Value τ) (other : Var Γ σ) (different : τ ≠ σ) :
    (env.set v value).get other = env.get other := by
  induction v generalizing σ with
  | here =>
      cases other with
      | here => exact False.elim (different rfl)
      | there other => rfl
  | there v ih =>
      cases other with
      | here => rfl
      | there other => exact ih env.tail value other different

/-- Any different typed variable is unchanged, including variables of a
different type. The condition concerns variable identity, not stored values. -/
theorem get_set_of_ne {Γ : List Ty} {τ σ : Ty} (env : Env Γ)
    (v : Var Γ τ) (value : Value τ) (other : Var Γ σ) (different : ¬HEq v other) :
    (env.set v value).get other = env.get other := by
  by_cases types : τ = σ
  · subst σ
    exact get_set_of_ne_same env v value other (fun same => different (heq_of_eq same))
  · exact get_set_of_type_ne env v value other types

/-- Exiting the updated innermost scope discards only that local update. -/
@[simp] theorem tail_set_here {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ))
    (value : Value τ) : (env.set .here value).tail = env.tail := rfl

/-- An outer-variable update survives leaving the innermost scope. -/
@[simp] theorem tail_set_there {Γ : List Ty} {τ σ : Ty} (env : Env (σ :: Γ))
    (v : Var Γ τ) (value : Value τ) :
    (env.set (.there v) value).tail = env.tail.set v value := rfl

end Env

/-- Independent source state: mathematical lexical values and the current shared heap. -/
structure State (Γ : List Ty) where
  locals : Env Γ
  heap : Heap

namespace State

/-- A state is determined by its actual locals and shared heap. -/
@[ext] theorem ext {Γ : List Ty} {left right : State Γ}
    (locals : left.locals = right.locals) (heap : left.heap = right.heap) : left = right := by
  cases left
  cases right
  cases locals
  cases heap
  rfl

/-- Enter a function with its actual arguments and the caller's current shared heap. -/
def enter {Γ Δ : List Ty} (state : State Γ) (args : Env Δ) : State Δ :=
  ⟨args, state.heap⟩

/-- Restore caller locals while retaining the callee's actual heap effects. -/
def restore {Γ Δ : List Ty} (caller : State Γ) (callee : State Δ) : State Γ :=
  ⟨caller.locals, callee.heap⟩

/-- Extend the current lexical scope without replacing the shared heap. -/
def cons {Γ : List Ty} {τ : Ty} (value : Value τ) (state : State Γ) : State (τ :: Γ) :=
  ⟨Env.cons value state.locals, state.heap⟩

/-- Leave one lexical scope, retaining actual outer-local and shared-heap changes. -/
def tail {Γ : List Ty} {τ : Ty} (state : State (τ :: Γ)) : State Γ :=
  ⟨state.locals.tail, state.heap⟩

/-- Update one current local without changing the current shared heap. -/
def set {Γ : List Ty} {τ : Ty} (state : State Γ) (v : Var Γ τ) (value : Value τ) : State Γ :=
  ⟨state.locals.set v value, state.heap⟩

@[simp] theorem locals_enter {Γ Δ : List Ty} (state : State Γ) (args : Env Δ) :
    (state.enter args).locals = args := rfl

@[simp] theorem heap_enter {Γ Δ : List Ty} (state : State Γ) (args : Env Δ) :
    (state.enter args).heap = state.heap := rfl

@[simp] theorem locals_restore {Γ Δ : List Ty} (caller : State Γ) (callee : State Δ) :
    (caller.restore callee).locals = caller.locals := rfl

@[simp] theorem heap_restore {Γ Δ : List Ty} (caller : State Γ) (callee : State Δ) :
    (caller.restore callee).heap = callee.heap := rfl

@[simp] theorem locals_cons {Γ : List Ty} {τ : Ty} (value : Value τ) (state : State Γ) :
    (cons value state).locals = Env.cons value state.locals := rfl

@[simp] theorem heap_cons {Γ : List Ty} {τ : Ty} (value : Value τ) (state : State Γ) :
    (cons value state).heap = state.heap := rfl

@[simp] theorem locals_tail {Γ : List Ty} {τ : Ty} (state : State (τ :: Γ)) :
    state.tail.locals = state.locals.tail := rfl

@[simp] theorem heap_tail {Γ : List Ty} {τ : Ty} (state : State (τ :: Γ)) :
    state.tail.heap = state.heap := rfl

@[simp] theorem locals_set {Γ : List Ty} {τ : Ty} (state : State Γ) (v : Var Γ τ)
    (value : Value τ) : (state.set v value).locals = state.locals.set v value := rfl

@[simp] theorem heap_set {Γ : List Ty} {τ : Ty} (state : State Γ) (v : Var Γ τ)
    (value : Value τ) : (state.set v value).heap = state.heap := rfl

/-- Introducing and immediately leaving a scope preserves the complete state. -/
@[simp] theorem tail_cons {Γ : List Ty} {τ : Ty} (value : Value τ) (state : State Γ) :
    (cons value state).tail = state := rfl

/-- Splitting and restoring the innermost binding preserves the actual shared heap. -/
@[simp] theorem cons_head_tail {Γ : List Ty} {τ : Ty} (state : State (τ :: Γ)) :
    cons state.locals.head state.tail = state := by
  apply State.ext
  · exact Env.cons_head_tail state.locals
  · rfl

/-- Dropping an updated inner local leaves the current outer state intact. -/
@[simp] theorem tail_set_here {Γ : List Ty} {τ : Ty} (state : State (τ :: Γ))
    (value : Value τ) : (state.set .here value).tail = state.tail := rfl

/-- Updates to outer locals survive scope exit together with the current heap. -/
@[simp] theorem tail_set_there {Γ : List Ty} {τ σ : Ty} (state : State (σ :: Γ))
    (v : Var Γ τ) (value : Value τ) :
    (state.set (.there v) value).tail = state.tail.set v value := rfl

end State

end Complexity.Language
