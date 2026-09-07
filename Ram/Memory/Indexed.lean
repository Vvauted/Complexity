/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Observation
import Mathlib.Logic.Function.Basic

/-!
# Ordinary indexed functions as memory models

`IndexedRep mem address values` describes selected RAM cells by an ordinary
function `values : ι → Word w`. The index can be `Fin n`, a product of finite
indices, or another existing mathematical type; no new vector or map datatype
is introduced. Reindexing is ordinary function composition, and a machine store
is mathlib's `Function.update` on the model.

The assertion by itself describes values, not ownership or allocation. A store
requires an injective address layout; `Source.IndexedAt` separately records that
the observed addresses belong to the source heap. Thus no-wrap, aliasing and
heap-access obligations stay explicit without being repeated in model proofs.
-/

namespace Ram

universe u v

/-- Selected memory cells have the values of an ordinary indexed function. -/
def IndexedRep {ι : Type u} (mem : Word w → Word w) (address : ι → Word w)
    (values : ι → Word w) : Prop :=
  ∀ i, mem (address i) = values i

namespace IndexedRep

variable {ι : Type u} {κ : Type v} {mem before after : Word w → Word w}
  {address : ι → Word w} {values other : ι → Word w}

theorem lookup (h : IndexedRep mem address values) (i : ι) :
    mem (address i) = values i := h i

/-- The whole model is an ordinary function equality, suitable for rewriting
any mathlib property without a second pointwise representation proof. -/
theorem contents_eq (h : IndexedRep mem address values) : mem ∘ address = values :=
  funext h

theorem iff_contents_eq : IndexedRep mem address values ↔ mem ∘ address = values :=
  ⟨contents_eq, fun h i => congrFun h i⟩

theorem of_contents (mem : Word w → Word w) (address : ι → Word w) :
    IndexedRep mem address (mem ∘ address) := fun _ => rfl

/-- The same observed cells cannot represent two different functions. -/
theorem eq (h : IndexedRep mem address values) (h' : IndexedRep mem address other) :
    values = other := h.contents_eq.symm.trans h'.contents_eq

theorem congr_mem (h : IndexedRep before address values)
    (hmem : ∀ i, after (address i) = before (address i)) :
    IndexedRep after address values := fun i => (hmem i).trans (h i)

/-- Restricting, permuting or reshaping a model uses existing functions. -/
theorem reindex (h : IndexedRep mem address values) (f : κ → ι) :
    IndexedRep mem (address ∘ f) (values ∘ f) := fun i => h (f i)

/-- A surjective reindexing loses no information. In particular this applies
to any mathlib `Equiv`, without inventing a representation-specific bijection. -/
theorem reindex_iff (f : κ → ι) (hf : Function.Surjective f) :
    IndexedRep mem (address ∘ f) (values ∘ f) ↔ IndexedRep mem address values := by
  refine ⟨?_, fun h => h.reindex f⟩
  intro h i
  obtain ⟨j, rfl⟩ := hf i
  exact h j

theorem predicate_iff (h : IndexedRep mem address values) (P : (ι → Word w) → Prop) :
    P (mem ∘ address) ↔ P values := by rw [h.contents_eq]

/-- A real one-word store is standard function update when indices do not
alias. The proof uses mathlib's update/composition theorem directly. -/
theorem store [DecidableEq ι] (h : IndexedRep mem address values)
    (hinj : Function.Injective address) (i : ι) (value : Word w) :
    IndexedRep (fun a => if a = address i then value else mem a) address
      (Function.update values i value) := by
  apply iff_contents_eq.mpr
  have updated := Function.update_comp_eq_of_injective mem hinj i value
  rw [h.contents_eq] at updated
  simpa only [Function.comp_def, Function.update_apply] using updated

/-- Updates outside the selected cells preserve the complete model. -/
theorem store_outside (h : IndexedRep mem address values) (storedAt value : Word w)
    (hout : ∀ i, address i ≠ storedAt) :
    IndexedRep (fun a => if a = storedAt then value else mem a) address values := by
  intro i
  simpa only [if_neg (hout i)] using h i

theorem setMem [DecidableEq ι] {s : State w}
    (h : IndexedRep s.mem address values) (hinj : Function.Injective address)
    (i : ι) (value : Word w) :
    IndexedRep (s.setMem (address i) value).mem address (Function.update values i value) :=
  h.store hinj i value

/-- The existing store instruction has the same model update; no additional
executable primitive or abstract cost annotation is introduced. -/
theorem exec_store [DecidableEq ι] {s : State w}
    (h : IndexedRep s.mem address values) (hinj : Function.Injective address)
    (i : ι) (addrReg src : Reg) (haddr : s.regs addrReg = address i) :
    IndexedRep (execInstr (.store addrReg src) s).mem address
      (Function.update values i (s.regs src)) := by
  simpa only [execInstr, State.next_mem, haddr] using h.setMem hinj i (s.regs src)

end IndexedRep

namespace Source

/-- An indexed model all of whose cells lie in the source-visible heap. -/
def IndexedAt {ι : Type u} (heapLimit : Nat) (address : ι → Word w)
    (values : ι → Word w) (s : State w) : Prop :=
  IndexedRep s.mem address values ∧ ∀ i, (address i).toNat < heapLimit

namespace IndexedAt

variable {ι : Type u} {κ : Type v} {heapLimit : Nat}
  {address : ι → Word w} {values : ι → Word w} {s t : State w}

theorem lookup (h : IndexedAt heapLimit address values s) (i : ι) :
    s.mem (address i) = values i := h.1.lookup i

theorem addr_lt (h : IndexedAt heapLimit address values s) (i : ι) :
    (address i).toNat < heapLimit := h.2 i

theorem contents_eq (h : IndexedAt heapLimit address values s) :
    s.mem ∘ address = values := h.1.contents_eq

theorem reindex (h : IndexedAt heapLimit address values s) (f : κ → ι) :
    IndexedAt heapLimit (address ∘ f) (values ∘ f) s :=
  ⟨h.1.reindex f, fun i => h.2 (f i)⟩

theorem setReg (h : IndexedAt heapLimit address values s) (dst : Reg) (value : Word w) :
    IndexedAt heapLimit address values (s.setReg dst value) := h

theorem setMem [DecidableEq ι] (h : IndexedAt heapLimit address values s)
    (hinj : Function.Injective address) (i : ι) (value : Word w) :
    IndexedAt heapLimit address (Function.update values i value)
      (s.setMem (address i) value) := ⟨h.1.store hinj i value, h.2⟩

theorem setMem_outside (h : IndexedAt heapLimit address values s) (storedAt value : Word w)
    (hout : ∀ i, address i ≠ storedAt) :
    IndexedAt heapLimit address values (s.setMem storedAt value) :=
  ⟨h.1.store_outside storedAt value hout, h.2⟩

theorem enter (h : IndexedAt heapLimit address values s) (args : List (Word w)) :
    IndexedAt heapLimit address values (s.enter args) := h

theorem leave (h : IndexedAt heapLimit address values s)
    (caller : State w) (dst : Reg) (result : Expr) :
    IndexedAt heapLimit address values (caller.leave s dst result) := h

/-- Only heap agreement is needed to move a model between source states. -/
theorem heapEqBelow (h : IndexedAt heapLimit address values s)
    (hmem : HeapEqBelow heapLimit s.mem t.mem) : IndexedAt heapLimit address values t :=
  ⟨h.1.congr_mem (fun i => (hmem _ (h.2 i)).symm), h.2⟩

end IndexedAt

/-- Any indexed model, including product-indexed matrices and finite maps,
is observable on the actual target state through the existing compiler bridge. -/
theorem State.Observes.indexed {ι : Type u} {heapLimit locals : Nat}
    {address : ι → Word w} {values : ι → Word w}
    {s : Source.State w} {t : Ram.State w}
    (ho : State.Observes heapLimit locals s t)
    (h : IndexedAt heapLimit address values s) : IndexedRep t.mem address values :=
  h.1.congr_mem (fun i => (ho.heap _ (h.2 i)).symm)

end Source
end Ram
