/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.IntInput
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInput

/-!
# RAM layouts for signed inputs

The existing scalar and pair-column initializations include every sign bit,
constructor field, object extent and address in their word-width scale.
Canonical `Int` views only transport these proved layouts; signs are not erased
and no new memory object or uncharged source operation is introduced.
-/

namespace Complexity.Program.RamInput

open Language

universe u

/-- Both constructor fields determine the existing scalar launch scale. -/
instance int : RamInput Int := comap Representation.intEquiv.toEmbedding

/-- Signed prefixes retain the physical tail and its width requirements. -/
instance intProd {β : Type u} [Input β] [RamInput β] : RamInput (Int × β) :=
  comap Input.intPrefix

/-- Integer arrays use the verified Boolean/natural column initialization. -/
instance arrayInt : RamInput (Array Int) :=
  comap Representation.intEquiv.toEmbedding.arrayMap

/-- Column objects and scalar fields stay in the same fixed prefix layout. -/
instance arrayIntProd {β : Type u} [Input β] [Input.PrefixClosed β] [RamInput β] :
    RamInput (Array Int × β) :=
  comap
    (Representation.intEquiv.toEmbedding.arrayMap.prodMap (Function.Embedding.refl β))

end Complexity.Program.RamInput
