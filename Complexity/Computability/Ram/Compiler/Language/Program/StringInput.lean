/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.StringInput
import Complexity.Computability.Ram.Compiler.Language.Program.RaggedArrayInput

/-!
# RAM input layouts for strings

Reuse the same natural buffers, row boundaries and source observations as the
fixed string input interface. The existing RAM certificates retain actual
character codes, addresses, extents and input-tail storage in their word-width
requirements. This supplies neither a source UTF-8 decoder nor an uncharged
string operation.
-/

namespace Complexity.Program.RamInput

open Language

universe u

instance string : RamInput String := comap Representation.stringEmbedding

instance stringProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (String × β) :=
  comap (Representation.stringEmbedding.prodMap (Function.Embedding.refl β))

instance arrayString : RamInput (Array String) := comap Representation.stringEmbedding.arrayMap

instance arrayStringProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (Array String × β) :=
  comap (Representation.stringEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end Complexity.Program.RamInput
