/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Loop
import Mathlib.Logic.Equiv.Defs

/-!
# Ordinary local values as a proof view of source blocks

`Stmt.observe` changes only the coordinates of the existing `Stmt.action`.
An equivalence represents the complete lexical environment by ordinary values,
for example nested products. Every normal, returning or faulting outcome keeps
the actual final locals and shared heap. Undefined observations still mean that
there is no finite source execution.

These coordinates are not source product values, a runtime callback or a second
interpreter. In particular, hidden and shadowed bindings cannot be discarded:
the supplied view is an equivalence on the whole environment. `Env.equivProd`
and `Env.equivUnit` build such views using ordinary products and Unit.

The native triple bridge has the same budget-free meaning as `TotalWP`.
`Stmt.observe_while` transports the already proved loop equation, retaining
guard effects on both exits, normal iteration and early body return. It is not
a definition of a host loop and is deliberately not a simp rule.
-/

namespace Complexity.Language

namespace Env

/-- One lexical binding and its remaining environment are an ordinary product. -/
def equivProd {Γ : List Ty} {τ : Ty} : Env (τ :: Γ) ≃ Value τ × Env Γ where
  toFun env := (env.head, env.tail)
  invFun values := Env.cons values.1 values.2
  left_inv env := cons_head_tail env
  right_inv _ := rfl

/-- An empty lexical environment has the unique ordinary Unit value. -/
def equivUnit : Env [] ≃ Unit where
  toFun _ := ()
  invFun _ := Env.empty
  left_inv env := by
    funext τ v
    cases v
  right_inv value := by
    cases value
    rfl

@[simp] theorem equivProd_apply {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ)) :
    equivProd env = (env.head, env.tail) := rfl

@[simp] theorem equivProd_symm_apply {Γ : List Ty} {τ : Ty} (values : Value τ × Env Γ) :
    equivProd.symm values = Env.cons values.1 values.2 := rfl

@[simp] theorem equivUnit_apply (env : Env []) : equivUnit env = () := rfl

@[simp] theorem equivUnit_symm_apply (value : Unit) : equivUnit.symm value = Env.empty := rfl

end Env

namespace Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty} {Locals : Type}

/-- Observe the same source block with ordinary, lossless local coordinates.
The only state transformed by the returned action is the actual shared heap;
the complete actual final locals are retained alongside every control outcome. -/
noncomputable def observe (view : Env Γ ≃ Locals) (stmt : Stmt signatures Γ result)
    (program : Program signatures) (locals : Locals) :
    StateT Heap Part (Control result × Locals) := fun heap =>
  (stmt.action program ⟨view.symm locals, heap⟩).map fun (control, finish) =>
    ((control, view finish.locals), finish.heap)

variable {view : Env Γ ≃ Locals} {stmt : Stmt signatures Γ result}
variable {program : Program signatures} {locals finalLocals : Locals} {heap finalHeap : Heap}
variable {control : Control result}

/-- Membership in the ordinary-values observation is exactly the same finite
execution, including its actual final state on returns and faults. -/
theorem mem_observe_iff :
    ((control, finalLocals), finalHeap) ∈ observe view stmt program locals heap ↔
      Exec program stmt ⟨view.symm locals, heap⟩
        ⟨view.symm finalLocals, finalHeap⟩ control := by
  constructor
  · intro member
    obtain ⟨⟨actualControl, finish⟩, execution, same⟩ := Part.mem_map_iff _ |>.mp member
    rcases finish with ⟨actualLocals, actualHeap⟩
    cases same
    simpa only [Equiv.symm_apply_apply] using mem_action_iff.mp execution
  · intro execution
    refine Part.mem_map_iff _ |>.mpr
      ⟨(control, ⟨view.symm finalLocals, finalHeap⟩), mem_action_iff.mpr execution, ?_⟩
    simp only [Equiv.apply_symm_apply]

/-- A result equation certifies finite execution of the original source block,
not a result reconstructed from a specification or an assumed termination. -/
theorem observe_eq_some_iff :
    observe view stmt program locals heap = Part.some ((control, finalLocals), finalHeap) ↔
      Exec program stmt ⟨view.symm locals, heap⟩
        ⟨view.symm finalLocals, finalHeap⟩ control :=
  Part.eq_some_iff.trans mem_observe_iff

/-- Unfold the actual source loop once in ordinary local coordinates. Guard
fallthrough remains a missing-return fault, and only a normal body completion
repeats at its actual final locals and heap. -/
theorem observe_while (view : Env Γ ≃ Locals) (program : Program signatures)
    (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result) (locals : Locals) :
    observe view (.while guard body) program locals = (do
      let (guardControl, afterGuard) ← observe view guard program locals
      match guardControl with
      | .returned false => pure (.normal, afterGuard)
      | .returned true =>
          let (bodyControl, afterBody) ← observe view body program afterGuard
          match bodyControl with
          | .normal => observe view (.while guard body) program afterBody
          | .returned value => pure (.returned value, afterBody)
          | .fault error => pure (.fault error, afterBody)
      | .normal => pure (.fault .missingReturn, afterGuard)
      | .fault error => pure (.fault error, afterGuard)) := by
  funext heap
  conv =>
    lhs
    unfold observe
    rw [action_while]
  simp only [observe, Bind.bind, Pure.pure, StateT.bind,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((guard.action program ⟨view.symm locals, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨guardControl, ⟨afterGuardLocals, afterGuardHeap⟩⟩
  cases guardControl with
  | normal =>
      simp only [Pure.pure, StateT.pure, Part.bind_some]
  | fault error =>
      simp only [Pure.pure, StateT.pure, Part.bind_some]
  | returned again =>
      cases again with
      | false =>
          simp only [Pure.pure, StateT.pure, Part.bind_some]
      | true =>
          simp only [observe, Bind.bind, StateT.bind,
            ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some, Equiv.symm_apply_apply]
          apply congrArg ((body.action program ⟨afterGuardLocals, afterGuardHeap⟩).bind)
          funext outcome
          rcases outcome with ⟨bodyControl, ⟨afterBodyLocals, afterBodyHeap⟩⟩
          cases bodyControl <;>
            simp only [observe, Pure.pure, StateT.pure,
              ← Part.bind_some_eq_map, Part.bind_some, Equiv.symm_apply_apply]

end Stmt

open scoped Part.TotalCorrectness

/-- Total correctness is the native triple of the ordinary local-values view.
The view preserves actual final locals and heap; `Control.Satisfies` rejects
faults, and the strict Part interpretation also rejects divergence. -/
theorem TotalWP.iff_triple_observe {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {Locals : Type} (view : Env Γ ≃ Locals)
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop}
    {locals : Locals} {heap : Heap} :
    TotalWP program stmt normal returned ⟨view.symm locals, heap⟩ ↔
      Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
        (Stmt.observe view stmt program locals) (fun current => ⟨current = heap⟩)
        (fun outcome finalHeap => ⟨outcome.1.Satisfies normal returned
          ⟨view.symm outcome.2, finalHeap⟩⟩, ⟨⟩) := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  constructor
  · rintro ⟨finish, control, execution, post⟩ current rfl
    refine ⟨((control, view finish.locals), finish.heap), ?_, ?_⟩
    · apply Stmt.mem_observe_iff.mpr
      simpa only [Equiv.symm_apply_apply] using execution
    · simpa only [Equiv.symm_apply_apply] using post
  · intro specification
    obtain ⟨⟨⟨control, finalLocals⟩, finalHeap⟩, member, post⟩ := specification heap rfl
    exact ⟨⟨view.symm finalLocals, finalHeap⟩, control, Stmt.mem_observe_iff.mp member, post⟩

end Complexity.Language
