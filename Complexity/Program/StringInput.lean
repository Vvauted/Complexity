/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.RaggedArrayInput
import Complexity.Language.Representation.String

/-!
# Fixed string inputs and outputs

Strings use the public contiguous Unicode code-point representation. String
arrays reuse the canonical row-boundary/payload convention, preserving row
order and empty rows. Prefix instances retain the complete following input.
These are preloaded invocation and final-heap observation interfaces, not free
source conversions or support for arbitrary string expressions in the frontend.
-/

namespace Complexity.Program

open Language

universe u

namespace Input

instance string : Input String := comap inferInstance Representation.stringEmbedding

instance stringProd {β : Type u} [Input β] [PrefixClosed β] : Input (String × β) :=
  comap inferInstance
    (Representation.stringEmbedding.prodMap (Function.Embedding.refl β))

instance arrayString : Input (Array String) :=
  comap inferInstance Representation.stringEmbedding.arrayMap

instance arrayStringProd {β : Type u} [Input β] [PrefixClosed β] :
    Input (Array String × β) :=
  comap inferInstance
    (Representation.stringEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

namespace PrefixClosed

instance string : PrefixClosed String := comap inferInstance Representation.stringEmbedding

instance stringProd {β : Type u} [Input β] [PrefixClosed β] : PrefixClosed (String × β) :=
  comap inferInstance
    (Representation.stringEmbedding.prodMap (Function.Embedding.refl β))

instance arrayString : PrefixClosed (Array String) :=
  comap inferInstance Representation.stringEmbedding.arrayMap

instance arrayStringProd {β : Type u} [Input β] [PrefixClosed β] :
    PrefixClosed (Array String × β) :=
  comap inferInstance
    (Representation.stringEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end PrefixClosed
end Input

namespace Output

instance string : Output String where
  type := .buffer .nat
  representation := Representation.string

instance arrayString : Output (Array String) where
  type := .prod (.buffer .nat) (.buffer .nat)
  representation := Representation.arrayString

end Output
end Complexity.Program
