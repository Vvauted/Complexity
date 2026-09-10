/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Heap.Shape

/-!
# Existing object roots in source values and environments

Rootedness only says that a buffer's object identifier denotes an existing
slot. It imposes no type, extent, scalar-range or separation condition. In
particular, rooted buffers may still fail a heap access. Scalars carry no
roots. These source predicates contain no machine addresses or runtime metadata.
-/

namespace Complexity.Language

/-- Every object identifier carried by a source value already exists. -/
@[simp] def ValueRooted (heap : Heap) : {τ : Ty} → Value τ → Prop
  | .nat, _ => True
  | .bool, _ => True
  | .unit, _ => True
  | .buffer _, buffer => buffer.Rooted heap

/-- Heap growth preserves the object roots of a retained source value. -/
theorem ValueRooted.mono {initial finish : Heap} {τ : Ty} {value : Value τ}
    (rooted : ValueRooted initial value) (growth : initial.ShapeExtends finish) :
    ValueRooted finish value := by
  cases τ with
  | nat | bool | unit => trivial
  | buffer kind => exact Buffer.Rooted.mono rooted growth

namespace Env

/-- All buffer-valued bindings refer to existing object slots. -/
def Rooted (env : Env Γ) (heap : Heap) : Prop :=
  ∀ {τ} (v : Var Γ τ), ValueRooted heap (env.get v)

namespace Rooted

/-- An empty environment retains no object roots. -/
@[simp] theorem empty (heap : Heap) : Env.empty.Rooted heap := by
  intro τ v
  cases v

/-- Adding a rooted value preserves rootedness of every lexical binding. -/
theorem cons {heap : Heap} {env : Env Γ} (rooted : env.Rooted heap)
    (value : Value τ) (valueRooted : ValueRooted heap value) :
    (Env.cons value env).Rooted heap := by
  intro σ v
  cases v with
  | here => exact valueRooted
  | there v => exact rooted v

/-- The innermost value retains an existing object identifier. -/
theorem head {heap : Heap} {env : Env (τ :: Γ)} (rooted : env.Rooted heap) :
    ValueRooted heap env.head := rooted .here

/-- Leaving a lexical scope retains the roots of the outer bindings. -/
theorem tail {heap : Heap} {env : Env (τ :: Γ)} (rooted : env.Rooted heap) :
    env.tail.Rooted heap := fun v => rooted (.there v)

/-- Root obligations decompose along the actual lexical environment. -/
@[simp] theorem cons_iff (heap : Heap) (value : Value τ) (env : Env Γ) :
    (Env.cons value env).Rooted heap ↔ ValueRooted heap value ∧ env.Rooted heap := by
  constructor
  · intro rooted
    exact ⟨rooted.head, rooted.tail⟩
  · rintro ⟨valueRooted, rooted⟩
    exact rooted.cons value valueRooted

/-- Heap growth also preserves suspended callers' source environments. -/
theorem mono {initial finish : Heap} {env : Env Γ} (rooted : env.Rooted initial)
    (growth : initial.ShapeExtends finish) : env.Rooted finish :=
  fun v => ValueRooted.mono (rooted v) growth

end Rooted
end Env

/-- Atoms retain an existing variable's roots or produce a root-free scalar. -/
theorem Atom.eval_rooted {heap : Heap} {env : Env Γ} (atom : Atom Γ τ)
    (rooted : env.Rooted heap) : ValueRooted heap (atom.eval env) := by
  cases atom with
  | var v => exact rooted v
  | nat | bool | unit => trivial

/-- Primitives cannot construct a new object identifier. -/
theorem Prim.eval_rooted {heap : Heap} {env : Env Γ} (prim : Prim Γ τ)
    (rooted : env.Rooted heap) : ValueRooted heap (prim.eval env) := by
  cases prim with
  | atom atom => exact atom.eval_rooted rooted
  | add | mul | sub | div | mod | eq | lt | le | length => trivial

/-- Actual call operands preserve the roots needed by the callee's environment. -/
theorem Args.eval_rooted {heap : Heap} {env : Env Γ} (args : Args Γ params)
    (rooted : env.Rooted heap) : (args.eval env).Rooted heap := by
  induction args with
  | nil => exact Env.Rooted.empty heap
  | cons atom rest ih => exact ih.cons _ (atom.eval_rooted rooted)

/-- Shared object cells are scalars and cannot introduce an object root. -/
theorem CellTy.toValue_rooted (heap : Heap) (kind : CellTy) (value : CellValue kind) :
    ValueRooted heap (kind.toValue value) := by
  cases kind <;> trivial

/-- A successful relative slice keeps the original object identifier, even
when that object's scalar type or the resulting view extent is invalid. -/
theorem Buffer.Rooted.slice {heap : Heap} {kind : CellTy} {buffer view : Buffer kind}
    {offset length : Nat} (rooted : buffer.Rooted heap)
    (sliced : buffer.slice offset length = .ok view) : view.Rooted heap := by
  unfold Buffer.slice at sliced
  split at sliced
  · cases sliced
    exact rooted
  · cases sliced

end Complexity.Language
