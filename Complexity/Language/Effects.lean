/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Semantics

/-!
# Preserving individual source locals

`Stmt.PreservesLocal` checks that a statement does not assign to a selected
typed lexical variable. Other locals and the shared heap may change. Scoped
bindings shift the selected variable, and calls inspect only their caller
continuation because the call boundary restores caller locals.

`Exec.get_eq` applies this structural condition to the actual finite execution,
including returns and faults. It lets a frontend certify fixed loop captures
without asking an algorithm author to prove that immutable bindings stay fixed.
Preserving a buffer descriptor does not imply preserving its shared contents.
This is a local frame condition, not another state or execution semantics.
-/

namespace Complexity.Language

namespace Var

/-- The lexical position, independent of the value stored at that position. -/
@[simp] def index {Γ : List Ty} {τ : Ty} : Var Γ τ → Nat
  | .here => 0
  | .there v => v.index + 1

/-- A typed variable is determined by its lexical position in its context. -/
theorem index_injective {Γ : List Ty} {τ : Ty} :
    Function.Injective (index (Γ := Γ) (τ := τ)) := by
  intro v
  induction v with
  | here =>
      intro other same
      cases other with
      | here => rfl
      | there other => simp [index] at same
  | there v ih =>
      intro other same
      cases other with
      | here => simp [index] at same
      | there other => exact congrArg Var.there (ih (Nat.add_right_cancel same))

/-- Compare positions before constructor injection introduces heterogeneous
equalities between the constructors' implicit context parameters. -/
@[simp 1100] theorem eq_iff_index_eq {Γ : List Ty} {τ : Ty} (v other : Var Γ τ) :
    v = other ↔ v.index = other.index :=
  ⟨congrArg index, fun same => index_injective same⟩

end Var

namespace Env

/-- Updating one lexical position preserves every different position, even
when the two variables have different source types. -/
theorem get_set_of_index_ne {Γ : List Ty} {τ σ : Ty} (env : Env Γ)
    (v : Var Γ τ) (value : Value τ) (other : Var Γ σ)
    (different : v.index ≠ other.index) :
    (env.set v value).get other = env.get other := by
  induction v generalizing σ with
  | here =>
      cases other with
      | here => exact False.elim (different rfl)
      | there other => rfl
  | there v ih =>
      cases other with
      | here => rfl
      | there other =>
          exact ih env.tail value other
            (fun same => different (congrArg (fun position : Nat => position + 1) same))

end Env

namespace Stmt

/-- A sufficient structural condition for preserving one lexical value.
Assignment compares lexical positions, not source types or stored values. Both branches
and both parts of a loop must preserve the variable; calls need no condition
on callee-local assignments. -/
@[simp] def PreservesLocal {signatures : List Signature} {Γ : List Ty} {result τ : Ty}
    (stmt : Stmt signatures Γ result) (v : Var Γ τ) : Prop :=
  match stmt with
  | .skip => True
  | .assign target _ => target.index ≠ v.index
  | .letPrim _ continuation => continuation.PreservesLocal (.there v)
  | .read _ _ continuation => continuation.PreservesLocal (.there v)
  | .write _ _ _ => True
  | .slice _ _ _ continuation => continuation.PreservesLocal (.there v)
  | .alloc _ _ continuation => continuation.PreservesLocal (.there v)
  | .scope body => body.PreservesLocal v
  | .call _ _ continuation => continuation.PreservesLocal (.there v)
  | .seq first second => first.PreservesLocal v ∧ second.PreservesLocal v
  | .ite _ yes no => yes.PreservesLocal v ∧ no.PreservesLocal v
  | .matchOption _ noneBranch someBranch =>
      noneBranch.PreservesLocal v ∧ someBranch.PreservesLocal (.there v)
  | .while guard body => guard.PreservesLocal v ∧ body.PreservesLocal v
  | .ret _ => True

/-- The existing all-locals condition is sufficient for any individual local.
The finer condition also permits assignments to other variables. -/
theorem NoLocalWrites.preservesLocal {signatures : List Signature} {Γ : List Ty}
    {result : Ty} {stmt : Stmt signatures Γ result} (unchanged : stmt.NoLocalWrites) :
    ∀ {τ : Ty} (v : Var Γ τ), stmt.PreservesLocal v := by
  revert unchanged
  induction stmt with
  | skip => intro _ τ v; trivial
  | assign => intro impossible; exact False.elim impossible
  | letPrim value continuation ih =>
      intro unchanged τ v
      exact ih unchanged (.there v)
  | read buffer index continuation ih =>
      intro unchanged τ v
      exact ih unchanged (.there v)
  | write => intro _ τ v; trivial
  | slice buffer offset length continuation ih =>
      intro unchanged τ v
      exact ih unchanged (.there v)
  | alloc length initial continuation ih =>
      intro unchanged τ v
      exact ih unchanged (.there v)
  | scope body ih =>
      intro unchanged τ v
      exact ih unchanged v
  | call fn args continuation ih =>
      intro unchanged τ v
      exact ih unchanged (.there v)
  | seq first second ihFirst ihSecond =>
      intro unchanged τ v
      exact ⟨ihFirst unchanged.1 v, ihSecond unchanged.2 v⟩
  | ite condition yes no ihYes ihNo =>
      intro unchanged τ v
      exact ⟨ihYes unchanged.1 v, ihNo unchanged.2 v⟩
  | matchOption value noneBranch someBranch ihNone ihSome =>
      intro unchanged τ v
      exact ⟨ihNone unchanged.1 v, ihSome unchanged.2 (.there v)⟩
  | «while» guard body ihGuard ihBody =>
      intro unchanged τ v
      exact ⟨ihGuard unchanged.1 v, ihBody unchanged.2 v⟩
  | ret => intro _ τ v; trivial

end Stmt

namespace Exec

/-- A structurally protected lexical value survives the actual execution.
The conclusion applies to normal, returning and faulting paths alike; neither
heap identity nor preservation of other locals is required. -/
theorem get_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) {τ : Ty} (v : Var Γ τ)
    (preserved : stmt.PreservesLocal v) :
    finish.locals.get v = entry.locals.get v := by
  revert τ
  induction execution with
  | skip => intro τ v _; rfl
  | assign target value entry =>
      intro τ v preserved
      exact Env.get_set_of_index_ne entry.locals target (value.eval entry.locals) v preserved
  | letPrim body ih =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there] using
        ih (.there v) preserved
  | read loaded body ih =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there] using
        ih (.there v) preserved
  | readFault => intro τ v _; rfl
  | write => intro τ v _; rfl
  | writeFault => intro τ v _; rfl
  | slice sliced body ih =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there] using
        ih (.there v) preserved
  | sliceFault => intro τ v _; rfl
  | alloc body ih =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there] using
        ih (.there v) preserved
  | scope body safe ih => intro τ v preserved; exact ih v preserved
  | scopeEscape body escapes ih => intro τ v preserved; exact ih v preserved
  | seqNormal head tail ihHead ihTail =>
      intro τ v preserved
      exact (ihTail v preserved.2).trans (ihHead v preserved.1)
  | seqReturn head ih => intro τ v preserved; exact ih v preserved.1
  | seqFault head ih => intro τ v preserved; exact ih v preserved.1
  | iteTrue test body ih => intro τ v preserved; exact ih v preserved.1
  | iteFalse test body ih => intro τ v preserved; exact ih v preserved.2
  | matchNone selected body ih => intro τ v preserved; exact ih v preserved.1
  | matchSome selected body ih =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there] using
        ih (.there v) preserved.2
  | whileFalse test ih => intro τ v preserved; exact ih v preserved.1
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      intro τ v preserved
      exact (ihRest v preserved).trans
        ((ihIteration v preserved.2).trans (ihTest v preserved.1))
  | whileReturn test iteration ihTest ihIteration =>
      intro τ v preserved
      exact (ihIteration v preserved.2).trans (ihTest v preserved.1)
  | whileFault test iteration ihTest ihIteration =>
      intro τ v preserved
      exact (ihIteration v preserved.2).trans (ihTest v preserved.1)
  | whileGuardFault test ih => intro τ v preserved; exact ih v preserved.1
  | whileGuardMissingReturn test ih => intro τ v preserved; exact ih v preserved.1
  | ret => intro τ v _; rfl
  | callReturn callee body ihCallee ihBody =>
      intro τ v preserved
      simpa only [State.locals_tail, Env.get_tail, State.locals_cons, Env.cons_there,
        State.locals_restore] using ihBody (.there v) preserved
  | callFault => intro τ v _; rfl
  | callMissingReturn => intro τ v _; rfl

end Exec

end Complexity.Language
