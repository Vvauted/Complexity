/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.CharInput
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInput

/-!
# RAM layouts for character inputs

Reuse the existing natural-field and array initialization with the same Unicode
code-point observation as the source interface. Word-width requirements include
the actual character codes, array extents and addresses; no byte truncation,
alphabet compression or free source operation is introduced.
-/

namespace Complexity.Program.RamInput

open Language

universe u

instance char : RamInput Char := comap Representation.charEmbedding

instance charProd {β : Type u} [Input β] [RamInput β] : RamInput (Char × β) :=
  comap (Representation.charEmbedding.prodMap (Function.Embedding.refl β))

instance arrayChar : RamInput (Array Char) := comap Representation.charEmbedding.arrayMap

instance arrayCharProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (Array Char × β) :=
  comap (Representation.charEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end Complexity.Program.RamInput
