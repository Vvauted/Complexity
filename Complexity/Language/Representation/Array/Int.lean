/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Array
import Complexity.Language.Representation.Scalar

/-!
# Integer arrays through their constructor columns

The existing canonical `Int` view is lifted elementwise over an array. Its two
actual columns contain the sign constructor and its natural field; negative
zero is impossible and `(true, 0)` denotes `-1`. Equal column lengths and
all contents are observed at the same heap. This is neither a host decoder
nor a source-level conversion; allocation and access require real operations.
-/

namespace Complexity.Language.Representation

/-- An integer array uses the existing Boolean/natural pair-column layout. -/
def arrayInt : Representation (Array Int) (.prod (.buffer .bool) (.buffer .nat)) :=
  (arrayProd (array .bool) (array .nat)).comap intEquiv.toEmbedding.arrayMap

@[simp] theorem arrayInt_rel (values : Array Int)
    (columns : Buffer .bool × Buffer .nat) (heap : Heap) :
    arrayInt.Rel values columns heap ↔
      (arrayProd (array .bool) (array .nat)).Rel (values.map intEquiv) columns heap :=
  Iff.rfl

/-- The sign column retains the entire integer array's actual length. -/
theorem arrayInt_size {values : Array Int} {columns : Buffer .bool × Buffer .nat}
    {heap : Heap} (observed : arrayInt.Rel values columns heap) :
    values.size = columns.1.length := by
  have size : (values.map intEquiv).size = columns.1.length := arrayProd_size observed
  simpa only [Array.size_map] using size

/-- Integer contents survive exactly the supplied frames of both real columns. -/
theorem Preserves.arrayInt {initial finish : Heap}
    (signs : (array .bool).Preserves initial finish)
    (fields : (array .nat).Preserves initial finish) :
    arrayInt.Preserves initial finish :=
  Preserves.comap intEquiv.toEmbedding.arrayMap (Preserves.arrayProd signs fields)

end Complexity.Language.Representation
