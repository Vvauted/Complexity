/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Restriction
import Complexity.Computability.Ram.Compiler.Language.Heap

/-!+# Encoded object extents under source shape extension

Mutable arrays retain their lengths and immutable nodes retain their complete
payloads and links. Both facts preserve the size of actual encoded storage.
These rules let arena framing and prefix reclamation treat all objects alike,
without assigning source object identifiers a machine address or a word bound.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Every old object has a current object of the same encoded extent. Arrays
may have changed values; immutable nodes retain their entire contents. -/
theorem heapObjectWords_size_of_shapeExtends {initial finish : Heap}
    (growth : initial.ShapeExtends finish) (placement : Nat → Word w)
    {object : Nat} {stored : HeapObject} (found : initial.objects[object]? = some stored) :
    ∃ current, finish.objects[object]? = some current ∧
      (heapObjectWords placement current).size = (heapObjectWords placement stored).size := by
  cases stored with
  | buffer kind values =>
      obtain ⟨current, currentFound, sameSize⟩ :=
        growth.objects (Heap.object?_eq_some_iff.mpr found)
      exact ⟨.buffer kind current, Heap.object?_eq_some_iff.mp currentFound, by
        simpa only [heapObjectWords_buffer_size] using sameSize⟩
  | node kind head tail =>
      exact ⟨.node kind head tail,
        Heap.node?_eq_some_iff.mp (growth.nodes (Heap.node?_eq_some_iff.mpr found)), rfl⟩

/-- A retained current object has an original object of the same encoded
extent. This recovers the old reservation bound without restoring old arrays. -/
theorem heapObjectWords_size_of_shapeExtends_of_lt {initial finish : Heap}
    (growth : initial.ShapeExtends finish) (placement : Nat → Word w)
    {object : Nat} {stored : HeapObject} (bound : object < initial.objects.size)
    (found : finish.objects[object]? = some stored) :
    ∃ previous, initial.objects[object]? = some previous ∧
      (heapObjectWords placement stored).size = (heapObjectWords placement previous).size := by
  cases stored with
  | buffer kind values =>
      obtain ⟨previous, previousFound, sameSize⟩ :=
        growth.objects_of_lt bound (Heap.object?_eq_some_iff.mpr found)
      exact ⟨.buffer kind previous, Heap.object?_eq_some_iff.mp previousFound, by
        simpa only [heapObjectWords_buffer_size] using sameSize⟩
  | node kind head tail =>
      exact ⟨.node kind head tail,
        Heap.node?_eq_some_iff.mp
          (growth.nodes_of_lt bound (Heap.node?_eq_some_iff.mpr found)), rfl⟩

end Ram.LanguageCompiler
