/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Component.Basic
import Complexity.Computability.Ram.Source.Linking

/-!
# Building reusable components from ordinary proofs

`Component.ofNamed` turns a named source program and its ordinary total contract
into a reusable component. A client proves the contract only at its required
heap capacity and call depth. Monotonicity supplies all larger surrounding
capacities automatically; clients do not have to reconstruct measured executions.
-/

namespace Ram.Component

universe u v

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

/-- Package a named program using the same contracts used for individual proofs.
The source, static validity, and resource bounds are all retained unchanged. -/
def ofNamed (bundle : Named.Bundle)
    (time heap depth size : Nat → Nat)
    (hvalid : LocalCompiler.Valid bundle.registers bundle.program bundle.main)
    (hsize : ∀ w x, domain w x → B.size (f x) ≤ size (A.size x))
    (hcontract : ∀ w x, domain w x →
      Source.Contract bundle.registers bundle.program (heap (A.size x)) (depth (A.size x))
        bundle.main (A.represents w x) (B.represents w (f x)) (fun _ => time (A.size x))) :
    Component A B f domain where
  locals := bundle.registers
  functions := bundle.program
  body := bundle.main
  valid := hvalid
  timeBound := time
  heapBound := heap
  depthBound := depth
  sizeBound := size
  size_le := hsize
  correct x hx s hs _ _ hH hd :=
    (((hcontract _ x hx).mono_heap hH).mono_depth hd) s hs

@[simp] theorem ofNamed_code (bundle : Named.Bundle)
    (time heap depth size : Nat → Nat)
    (hvalid : LocalCompiler.Valid bundle.registers bundle.program bundle.main)
    (hsize : ∀ w x, domain w x → B.size (f x) ≤ size (A.size x))
    (hcontract : ∀ w x, domain w x →
      Source.Contract bundle.registers bundle.program (heap (A.size x)) (depth (A.size x))
        bundle.main (A.represents w x) (B.represents w (f x)) (fun _ => time (A.size x))) :
    (ofNamed bundle time heap depth size hvalid hsize hcontract).code =
      LocalCompiler.rawLink bundle.registers bundle.program bundle.main := rfl

end Ram.Component
