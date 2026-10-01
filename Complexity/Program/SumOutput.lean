/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Basic

/-!+# Fixed sum outputs

A sum observes exactly one of two existing output layouts at the actual return
heap. It reuses `Representation.sum` and the core's option/product operations;
neither an absent payload nor an invalid pair supplies default contents.

This instance fixes an output convention, not a decoder, new source primitive,
native `Sum` elaborator, or free conversion. Source constructors use the existing
`some`/`none` and pair operations, whose lowering retains their ordinary costs.
Heap-backed payloads remain observations at return time, not frozen snapshots.
-/

namespace Complexity.Program.Output

open Language

universe u v

/-- Observe exactly one actual payload through the existing mutually exclusive
option/product representation. -/
instance sum {α : Type u} {β : Type v} [Output α] [Output β] : Output (Sum α β) where
  type := .prod (.option (Output.type α)) (.option (Output.type β))
  representation := Representation.sum
    (Output.representation (β := α)) (Output.representation (β := β))

/-- Returning the left constructor retains the payload's ordinary observation. -/
@[simp] theorem sum_inl {α : Type u} {β : Type v} [Output α] [Output β]
    (value : α) (actual : Value (Output.type α)) (heap : Heap) :
    (Output.representation (β := Sum α β)).Rel (.inl value) (some actual, none) heap ↔
      (Output.representation (β := α)).Rel value actual heap := Iff.rfl

/-- Returning the right constructor retains the payload's ordinary observation. -/
@[simp] theorem sum_inr {α : Type u} {β : Type v} [Output α] [Output β]
    (value : β) (actual : Value (Output.type β)) (heap : Heap) :
    (Output.representation (β := Sum α β)).Rel (.inr value) (none, some actual) heap ↔
      (Output.representation (β := β)).Rel value actual heap := Iff.rfl

end Complexity.Program.Output
