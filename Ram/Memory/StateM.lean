/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Memory.Contracts
import Ram.Verification.StateM

/-!
# Native stateful models for indexed loads and stores

An indexed memory model is the ordinary function `ι → Word w`. Its operations
use native `StateM` `get`/`pure` and `modify`, so abstract clients can use Std's
existing triples and `mvcgen`. The refinements below supply the RAM side using
the existing safe read/store contracts, without a new evaluator or cost model.

The actual entry state is captured only in representation predicates. Exact
endpoint equalities retain other registers, memory and I/O for subsequent
operations. In particular, reading into a temporary does not discard facts
about the registers holding later addresses. The index and stored value are
ghost parameters; the source expressions are fixed and must evaluate to them.
-/

namespace Ram.Source.Indexed

variable {ι : Type} {heapLimit depth : Nat} {program : Program}
variable {layout : ι → Word w}

/-- One actual load refines native state observation. The abstract state is
unchanged, and the complete concrete endpoint preserves the caller's frame. -/
theorem read_stateM (entry : State w) (i : ι) (dst : Reg) (address : Expr) :
    Refines program heapLimit depth (.assign dst (.load address))
      (fun values s => s = entry ∧ IndexedAt heapLimit layout values s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧ s.eval address = layout i)
      (fun result finish => finish = entry.setReg dst result.1 ∧
        IndexedAt heapLimit layout result.2 finish)
      ((do
        let values ← get
        pure (values i)) : StateM (ι → Word w) (Word w)).run := by
  rintro values s ⟨same, represented, reads, addressEq⟩
  subst s
  obtain ⟨finish, execution, endpoint, result⟩ :=
    (read_contract (program := program) (heapLimit := heapLimit) (depth := depth)
      (layout := layout) (values := values) i dst address) entry
      ⟨represented, reads, addressEq⟩
  exact ⟨finish, execution, endpoint, result⟩

/-- One actual store refines native modification by mathlib's function update.
No registers change; the singleton-complement frame also retains unrelated
heap objects through the existing frame rules. The layout must not alias. -/
theorem store_stateM [DecidableEq ι] (entry : State w)
    (injective : Function.Injective layout) (i : ι) (address value : Expr) (stored : Word w) :
    Refines program heapLimit depth (.store address value)
      (fun values s => s = entry ∧ IndexedAt heapLimit layout values s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧ value.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = layout i ∧ s.eval value = stored)
      (fun result finish => finish = entry.setMem (layout i) stored ∧
        IndexedAt heapLimit layout result.2 finish ∧
        Set.EqOn finish.mem entry.mem ({layout i} : Set (Word w))ᶜ)
      (modify (fun values : ι → Word w => Function.update values i stored) :
        StateM (ι → Word w) PUnit).run := by
  rintro values s ⟨same, represented, addressReads, valueReads, addressEq, valueEq⟩
  subst s
  obtain ⟨finish, execution, endpoint, result, frame⟩ :=
    (store_contract (program := program) (heapLimit := heapLimit) (depth := depth)
      (layout := layout) (values := values) injective i address value stored) entry
      ⟨represented, addressReads, valueReads, addressEq, valueEq⟩
  exact ⟨finish, execution, endpoint, result, frame⟩

end Ram.Source.Indexed
