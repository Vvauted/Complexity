/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayInput
import Complexity.Language.Representation.Array.Int
import Complexity.Language.Representation.RaggedArray

/-!
# Fixed integer inputs and outputs

Integers reuse their established constructor view, not absolute values or a
task-specific natural-number code. Array columns use the same preloaded object
conventions as Boolean/natural pair arrays. Prefixes retain the ordered layout
and the exact tail heap. These are fixed invocation/observation interfaces;
they do not implement integer expressions or charge host preprocessing as free.
-/

namespace Complexity.Program

open Language

universe u

namespace Input

/-- A signed scalar exposes its two canonical constructor fields. -/
instance int : Input Int := comap inferInstance Representation.intEquiv.toEmbedding

/-- Expose the integer's fields before an unchanged input tail. -/
def intPrefix {β : Type u} : (Int × β) ↪ Bool × Nat × β :=
  (Representation.intEquiv.toEmbedding.prodMap (Function.Embedding.refl β)).trans
    (Equiv.prodAssoc Bool Nat β).toEmbedding

/-- Signed scalar prefixes use the same ordered scalar parameters. -/
instance intProd {β : Type u} [Input β] : Input (Int × β) :=
  comap inferInstance intPrefix

/-- Every array element retains its sign and natural constructor field. -/
instance arrayInt : Input (Array Int) :=
  comap inferInstance Representation.intEquiv.toEmbedding.arrayMap

/-- Integer-array fields reuse both actual columns before the existing tail. -/
instance arrayIntProd {β : Type u} [Input β] [PrefixClosed β] :
    Input (Array Int × β) :=
  comap inferInstance
    (Representation.intEquiv.toEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

namespace PrefixClosed

instance int : PrefixClosed Int :=
  comap inferInstance Representation.intEquiv.toEmbedding

instance intProd {β : Type u} [Input β] [PrefixClosed β] : PrefixClosed (Int × β) :=
  comap inferInstance Input.intPrefix

instance arrayInt : PrefixClosed (Array Int) :=
  comap inferInstance Representation.intEquiv.toEmbedding.arrayMap

instance arrayIntProd {β : Type u} [Input β] [PrefixClosed β] :
    PrefixClosed (Array Int × β) :=
  comap inferInstance
    (Representation.intEquiv.toEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end PrefixClosed

end Input

namespace Output

/-- Observe the canonical integer carried by the actual returned scalar pair. -/
instance int : Output Int where
  type := .prod .bool .nat
  representation := Representation.int

/-- Observe every integer through the actual final-heap pair of columns. -/
instance arrayInt : Output (Array Int) where
  type := .prod (.buffer .bool) (.buffer .nat)
  representation := Representation.arrayInt

/-- Nested integer rows share one boundary buffer and the canonical integer
columns. This observes existing returned storage; it does not copy rows. -/
instance raggedArrayInt : Output (Array (Array Int)) where
  type := .prod (.buffer .nat) (.prod (.buffer .bool) (.buffer .nat))
  representation := Representation.raggedArrayOf Representation.arrayInt

end Output

end Complexity.Program
