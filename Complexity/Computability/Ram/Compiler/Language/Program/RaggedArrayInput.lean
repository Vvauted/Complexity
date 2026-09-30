/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.RaggedArrayInput
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInput

/-!
# RAM inputs for nested arrays

The existing array arena stores both cumulative boundaries and every payload
cell. Its width scale includes both arrays and their structural cursors. Empty
rows remain visible through repeated boundaries; no row is dropped or decoded
by an uncharged host operation during source execution.
-/

namespace Complexity.Program.RamInput

universe u v

/-- Reuse the proved two-array physical layout, including its word-width scale. -/
instance raggedArray {α : Type u} [Input (Array Nat × Array α)]
    [RamInput (Array Nat × Array α)] : RamInput (Array (Array α)) :=
  RamInput.comap Array.flattenEmbedding

/-- A nested-array field retains the existing physical layout of all tail fields. -/
instance raggedArrayProd {α : Type u} {β : Type v} [Input (Array Nat × Array α × β)]
    [RamInput (Array Nat × Array α × β)] : RamInput (Array (Array α) × β) :=
  RamInput.comap Input.raggedArrayPrefix

end Complexity.Program.RamInput
