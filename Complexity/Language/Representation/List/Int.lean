/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List.Prod
import Complexity.Language.Representation.Scalar
import Mathlib.Logic.Equiv.List

/-!
# Integer lists through real linked constructor fields

The canonical integer constructor view is lifted elementwise to two synchronized
linked chains. Each signed cons uses a Boolean node and a natural node;
`(true, 0)` denotes `-1`, with no negative-zero encoding. Both chains observe
the same list at the actual heap. This representation does not implement source
operations or give a free executable decoder.
-/

namespace Complexity.Language.Representation

/-- Integer lists use actual Boolean/natural chains and the canonical Int view. -/
def listInt : Representation (List Int)
    (.prod (.option (.node .bool)) (.option (.node .nat))) :=
  (listProd (list .bool) (list .nat)).comap
    (Equiv.listEquivOfEquiv intEquiv).toEmbedding

@[simp] theorem listInt_rel (values : List Int)
    (roots : Option (NodeRef .bool) × Option (NodeRef .nat)) (heap : Heap) :
    listInt.Rel values roots heap ↔
      (listProd (list .bool) (list .nat)).Rel (values.map intEquiv) roots heap :=
  Iff.rfl

/-- The empty signed list has two absent roots and allocates nothing. -/
theorem listInt_nil (heap : Heap) : listInt.Rel [] (none, none) heap :=
  listProd_nil .bool .nat heap

/-- A signed cons allocates both constructor fields and shares both old tails. -/
theorem listInt_cons (head : Int) {values : List Int}
    {tail : Option (NodeRef .bool) × Option (NodeRef .nat)} {heap : Heap}
    (observed : listInt.Rel values tail heap) :
    let first := heap.cons (intEquiv head).1 tail.1
    let second := first.2.cons (intEquiv head).2 tail.2
    listInt.Rel (head :: values) (some first.1, some second.1) second.2 :=
  listProd_cons (left := .bool) (right := .nat) (intEquiv head) observed

/-- Preserving immutable nodes preserves all existing signed-list observations. -/
theorem Preserves.listInt {initial finish : Heap}
    (shape : initial.ShapeExtends finish) :
    listInt.Preserves initial finish :=
  Preserves.comap (Equiv.listEquivOfEquiv intEquiv).toEmbedding
    (Preserves.listProd (Preserves.list .bool shape) (Preserves.list .nat shape))

end Complexity.Language.Representation
