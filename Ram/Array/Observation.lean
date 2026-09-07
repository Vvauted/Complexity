/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Contracts
import Ram.Array.TwoBuffer
import Ram.Observation

/-!
# Observing array contracts on the actual machine

Source-visible data agreement transfers a represented array to target memory.
Agreement at both endpoints also transfers a source array frame, but only
inside the observed heap. Compiler-private stack words are deliberately not
included in that conclusion. Neither lemma assumes a particular program or
machine status; completed compiler executions supply the same observations.
-/

namespace Ram.Source.State.Observes

/-- A represented source array is present in the observed target memory. -/
theorem array {heapLimit locals : Nat} {base : Word w} {xs : List (Word w)}
    {s : Source.State w} {t : Ram.State w}
    (ho : Observes heapLimit locals s t) (ha : ArrayAt heapLimit base xs s) :
    ArrayRep t.mem base xs := by
  refine ⟨ha.1.fits, ?_⟩
  intro i hi
  exact (ho.heap _ (ha.addr_lt hi)).symm.trans (ha.1.lookup i hi)

/-- An array frame is observable between two matching endpoints only below
their heap boundary. The endpoints need not have the same local-register bound. -/
theorem arrayFrame {heapLimit entryLocals finishLocals length : Nat} {base : Word w}
    {sourceEntry sourceFinish : Source.State w} {entry finish : Ram.State w}
    (ho : Observes heapLimit finishLocals sourceFinish finish)
    (he : Observes heapLimit entryLocals sourceEntry entry)
    (hf : ArrayFrame base length sourceEntry.mem sourceFinish.mem) :
    ∀ address, address.toNat < heapLimit →
      address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
        finish.mem address = entry.mem address := by
  intro address ha hout
  exact (ho.heap address ha).symm.trans ((hf address hout).trans (he.heap address ha))

/-- A source/scratch frame transfers only within the shared visible heap,
just like a single-array frame. Both actual endpoint states are retained. -/
theorem twoBufferFrame {heapLimit entryLocals finishLocals firstLen secondLen : Nat}
    {first second : Word w} {sourceEntry sourceFinish : Source.State w}
    {entry finish : Ram.State w}
    (ho : Observes heapLimit finishLocals sourceFinish finish)
    (he : Observes heapLimit entryLocals sourceEntry entry)
    (hf : TwoBufferFrame first firstLen second secondLen sourceEntry.mem sourceFinish.mem) :
    ∀ address, address.toNat < heapLimit →
      (address.toNat < first.toNat ∨ first.toNat + firstLen ≤ address.toNat) →
      (address.toNat < second.toNat ∨ second.toNat + secondLen ≤ address.toNat) →
        finish.mem address = entry.mem address := by
  intro address ha hfirst hsecond
  exact (ho.heap address ha).symm.trans
    ((hf address hfirst hsecond).trans (he.heap address ha))

end Ram.Source.State.Observes
