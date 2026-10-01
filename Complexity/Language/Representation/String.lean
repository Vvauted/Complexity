/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.RaggedArray
import Complexity.Language.Representation.Scalar
import Init.Data.List.ToArray
import Init.Data.String.Basic

/-!
# Strings as contiguous Unicode scalar values

The mathematical value remains an ordinary Lean `String`. Its source layout
stores every Unicode scalar value, in order, in an existing natural buffer.
This is a code-point layout, not Lean's UTF-8 byte layout. In particular a
character index is not a `String.Pos.Raw` byte position.

Arrays of strings use the existing shared row boundaries and flattened payload.
Empty strings and embedded null characters are retained. These observations
implement no string operation, host conversion or arbitrary decoder; source
operations and their costs require separate checked implementations.
-/

namespace Complexity.Language.Representation

/-- The complete character sequence, with no alphabet restriction or filtering. -/
def stringChars : String ↪ Array Char where
  toFun value := value.toList.toArray
  inj' _ _ same := String.toList_injective (List.toArray_inj same)

/-- Each stored natural is the corresponding character's Unicode scalar code. -/
def stringEmbedding : String ↪ Array Nat :=
  stringChars.trans charEmbedding.arrayMap

@[simp] theorem stringEmbedding_size (value : String) :
    (stringEmbedding value).size = value.length := by
  change (value.toList.toArray.map Char.toNat).size = value.length
  simp only [Array.size_map, List.size_toArray, String.length_toList]

/-- Observe the complete string in the actual buffer at the current heap. -/
def string : Representation String (.buffer .nat) :=
  (array .nat).comap stringEmbedding

@[simp] theorem string_rel (value : String) (buffer : Buffer .nat) (heap : Heap) :
    string.Rel value buffer heap ↔ buffer.Contents heap (stringEmbedding value) := Iff.rfl

/-- The descriptor counts characters, not encoded UTF-8 bytes. -/
theorem string_length {value : String} {buffer : Buffer .nat} {heap : Heap}
    (observed : string.Rel value buffer heap) : value.length = buffer.length := by
  have sized := observed.size_eq
  simpa only [stringEmbedding_size] using sized

/-- String arrays retain every row, including repeated empty rows. -/
def arrayString : Representation (Array String) (.prod (.buffer .nat) (.buffer .nat)) :=
  (raggedArray .nat).comap stringEmbedding.arrayMap

end Complexity.Language.Representation
