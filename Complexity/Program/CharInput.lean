/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ArrayInput
import Complexity.Language.Representation.Scalar

/-!
# Fixed character inputs and outputs

Ordinary `Char` values use Lean's Unicode scalar codes in the existing natural
layout. Arrays retain every character and their actual length. These fixed
invocation and final-heap observations perform no source-level decoding;
construction, comparison and access need their own real source operations.
-/

namespace Complexity.Program

open Language

universe u

namespace Input

instance char : Input Char := comap inferInstance Representation.charEmbedding

instance charProd {β : Type u} [Input β] : Input (Char × β) :=
  comap inferInstance (Representation.charEmbedding.prodMap (Function.Embedding.refl β))

instance arrayChar : Input (Array Char) :=
  comap inferInstance Representation.charEmbedding.arrayMap

instance arrayCharProd {β : Type u} [Input β] [PrefixClosed β] : Input (Array Char × β) :=
  comap inferInstance
    (Representation.charEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

namespace PrefixClosed

instance char : PrefixClosed Char := comap inferInstance Representation.charEmbedding

instance charProd {β : Type u} [Input β] [PrefixClosed β] : PrefixClosed (Char × β) :=
  comap inferInstance (Representation.charEmbedding.prodMap (Function.Embedding.refl β))

instance arrayChar : PrefixClosed (Array Char) :=
  comap inferInstance Representation.charEmbedding.arrayMap

instance arrayCharProd {β : Type u} [Input β] [PrefixClosed β] : PrefixClosed (Array Char × β) :=
  comap inferInstance
    (Representation.charEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end PrefixClosed
end Input

namespace Output

instance char : Output Char where
  type := .nat
  representation := Representation.char

instance arrayChar : Output (Array Char) where
  type := .buffer .nat
  representation := (Representation.array .nat).comap Representation.charEmbedding.arrayMap

end Output
end Complexity.Program
