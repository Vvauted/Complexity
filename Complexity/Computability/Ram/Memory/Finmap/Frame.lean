/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Finmap.StateM
import Complexity.Computability.Ram.Verification.StateM.Frame

/-!
# Finite-map operations inside a larger native state

The existing insertion-and-lookup block can be used while another mathematical
object remains in the workspace. Its native state is the ordinary product of
the finite map and the additional model. The source code, returned option,
exact endpoint and proved two-cell frame are unchanged.

`insert_lookup_stateM_frame` accepts any localized heap representation.
`insert_lookup_stateM_indexed` supplies localization for an ordinary indexed
function, including its source-heap bounds. Finite arrays and product-indexed
matrix views can therefore be retained without a fresh pointwise frame proof.
Disjointness is required only from the inserted key's two written cells, not
from the whole finite-map layout. This is endpoint preservation, not exclusive
ownership, heap/model bijectivity, or a claim about every intermediate state.
-/

namespace Ram.Source.Finmap

variable {κ : Type} [DecidableEq κ] {heapLimit depth : Nat} {program : Program}
variable {layout : κ × Bool → Word w}

/-- Retain an arbitrary localized heap model alongside the existing native
finite-map insertion and lookup. The ordinary `modifyGet` only describes the
mathematical product state; it adds no RAM primitive or instruction cost. -/
theorem insert_lookup_stateM_frame {γ : Type}
    (entry : State w) (key : κ) (value marker : Word w)
    (payloadReg valueReg flagReg markerReg found dst : Reg)
    (injective : Function.Injective layout) (nonzero : marker ≠ 0)
    (payload : entry.regs payloadReg = layout (key, true))
    (stored : entry.regs valueReg = value)
    (flag : entry.regs flagReg = layout (key, false))
    (presence : entry.regs markerReg = marker)
    (payload_available : payloadReg ≠ found) (found_retained : found ≠ dst)
    (observed : γ → Set (Word w)) (heapModel : γ → (Word w → Word w) → Prop)
    (depends : ∀ z before after, Set.EqOn after before (observed z) →
      heapModel z before → heapModel z after) :
    let updated := (entry.setMem (layout (key, true)) value).setMem
      (layout (key, false)) marker
    let native : StateM (Finmap (fun _ : κ => Word w)) (Option (Word w)) := do
      modify (fun map => map.insert key value)
      let map ← get
      pure (map.lookup key)
    Refines program heapLimit depth
      (.seq (.seq (.store (.var payloadReg) (.var valueReg))
        (.store (.var flagReg) (.var markerReg)))
        (lookup flagReg payloadReg found dst))
      (fun (map, z) s => s = entry ∧ FinmapAt heapLimit layout map s ∧
        heapModel z s.mem ∧ Disjoint (observed z)
          ({layout (key, true), layout (key, false)} : Set (Word w)))
      (fun result finish => finish = (updated.setReg found marker).setReg dst value ∧
        FinmapAt heapLimit layout result.2.1 finish ∧
        (if finish.regs found = 0 then none else some (finish.regs dst)) = result.1 ∧
        result.1 = some value ∧
        Set.EqOn finish.mem entry.mem
          ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ ∧
        heapModel result.2.2 finish.mem)
      (modifyGet (fun (map, z) =>
        let result := native.run map
        (result.1, (result.2, z))) :
        StateM (Finmap (fun _ : κ => Word w) × γ) (Option (Word w))).run := by
  dsimp only
  have implementation := insert_lookup_stateM (program := program) (heapLimit := heapLimit)
    (depth := depth) (layout := layout) entry key value marker
    payloadReg valueReg flagReg markerReg found dst injective nonzero
    payload stored flag presence payload_available found_retained
  have framed := implementation.stateM_frame_heap observed
    (fun _ => ({layout (key, true), layout (key, false)} : Set (Word w)))
    heapModel depends (by
      intro map start finish represented _ post
      simpa only [represented.1] using post.2.2.2.2)
  simpa only [and_assoc] using framed

/-- Preserve an unrelated indexed object through insertion and lookup, using
its standard address range. The additional model retains `IndexedAt`, including
all source-heap bounds needed by later reads or writes. -/
theorem insert_lookup_stateM_indexed {ι : Type}
    (entry : State w) (key : κ) (value marker : Word w)
    (payloadReg valueReg flagReg markerReg found dst : Reg)
    (injective : Function.Injective layout) (nonzero : marker ≠ 0)
    (payload : entry.regs payloadReg = layout (key, true))
    (stored : entry.regs valueReg = value)
    (flag : entry.regs flagReg = layout (key, false))
    (presence : entry.regs markerReg = marker)
    (payload_available : payloadReg ≠ found) (found_retained : found ≠ dst)
    (otherLayout : ι → Word w) :
    let updated := (entry.setMem (layout (key, true)) value).setMem
      (layout (key, false)) marker
    let native : StateM (Finmap (fun _ : κ => Word w)) (Option (Word w)) := do
      modify (fun map => map.insert key value)
      let map ← get
      pure (map.lookup key)
    Refines program heapLimit depth
      (.seq (.seq (.store (.var payloadReg) (.var valueReg))
        (.store (.var flagReg) (.var markerReg)))
        (lookup flagReg payloadReg found dst))
      (fun (map, values) s => s = entry ∧ FinmapAt heapLimit layout map s ∧
        IndexedAt heapLimit otherLayout values s ∧ Disjoint (Set.range otherLayout)
          ({layout (key, true), layout (key, false)} : Set (Word w)))
      (fun result finish => finish = (updated.setReg found marker).setReg dst value ∧
        FinmapAt heapLimit layout result.2.1 finish ∧
        (if finish.regs found = 0 then none else some (finish.regs dst)) = result.1 ∧
        result.1 = some value ∧
        Set.EqOn finish.mem entry.mem
          ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ ∧
        IndexedAt heapLimit otherLayout result.2.2 finish)
      (modifyGet (fun (map, values) =>
        let result := native.run map
        (result.1, (result.2, values))) :
        StateM (Finmap (fun _ : κ => Word w) × (ι → Word w)) (Option (Word w))).run := by
  exact insert_lookup_stateM_frame entry key value marker
    payloadReg valueReg flagReg markerReg found dst injective nonzero
    payload stored flag presence payload_available found_retained
    (fun _ => Set.range otherLayout)
    (fun values mem => IndexedRep mem otherLayout values ∧
      ∀ i, (otherLayout i).toNat < heapLimit)
    (fun _ _ _ same represented => ⟨represented.1.congr_eqOn same, represented.2⟩)

end Ram.Source.Finmap
