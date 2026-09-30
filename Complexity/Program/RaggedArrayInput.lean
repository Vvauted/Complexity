/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayInput
import Complexity.Language.Representation.RaggedArray

/-!
# Fixed nested-array inputs and outputs

Nested scalar arrays reuse two preloaded array objects: row boundaries and
payload. This is a lossless, order-preserving invocation convention, not free
algorithmic preprocessing. Constructing the same layout during execution still
requires real source operations and their costs. Returned layouts are observed
at the actual final heap; this module does not copy or allocate output data.
-/

namespace Complexity.Program

universe u v

namespace Input

/-- Fix the boundary/payload layout using the existing array input conventions. -/
instance raggedArray {α : Type u} [Input (Array Nat × Array α)] :
    Input (Array (Array α)) := Input.comap inferInstance Array.flattenEmbedding

/-- Expose row boundaries and payload while retaining the following input fields. -/
def raggedArrayPrefix {α : Type u} {β : Type v} :
    (Array (Array α) × β) ↪ Array Nat × Array α × β :=
  (Array.flattenEmbedding.prodMap (Function.Embedding.refl β)).trans
    (Equiv.prodAssoc (Array Nat) (Array α) β).toEmbedding

/-- Nested arrays compose with the remaining fixed input layout. -/
instance raggedArrayProd {α : Type u} {β : Type v}
    [Input (Array Nat × Array α × β)] : Input (Array (Array α) × β) :=
  Input.comap inferInstance raggedArrayPrefix

namespace PrefixClosed

instance raggedArray {α : Type u} [Input (Array Nat × Array α)]
    [PrefixClosed (Array Nat × Array α)] : PrefixClosed (Array (Array α)) :=
  PrefixClosed.comap inferInstance Array.flattenEmbedding

instance raggedArrayProd {α : Type u} {β : Type v} [Input (Array Nat × Array α × β)]
    [PrefixClosed (Array Nat × Array α × β)] : PrefixClosed (Array (Array α) × β) :=
  PrefixClosed.comap inferInstance Input.raggedArrayPrefix

end PrefixClosed
end Input

namespace Output

/-- Returned natural rows are observed through actual final-heap slices. -/
instance raggedArrayNat : Output (Array (Array Nat)) where
  type := .prod (.buffer .nat) (.buffer .nat)
  representation := Language.Representation.raggedArray .nat

/-- Returned Boolean rows use the same boundary convention and Boolean payload. -/
instance raggedArrayBool : Output (Array (Array Bool)) where
  type := .prod (.buffer .nat) (.buffer .bool)
  representation := Language.Representation.raggedArray .bool

end Output
end Complexity.Program
