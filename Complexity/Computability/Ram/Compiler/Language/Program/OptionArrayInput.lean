/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.OptionArrayInput
import Complexity.Computability.Ram.Compiler.Language.Program.IntInput

/-!
# RAM input layouts for optional-element arrays

Reuse the actual presence/payload column initialization, including all object
extents, addresses and payload word ranges. The mathematical input view does
not supply an uncharged operation within a running program.
-/

namespace Complexity.Program.RamInput

open Language

universe u v

instance arrayOption {α : Type u} [Inhabited α] [Input (Array (Bool × α))]
    [RamInput (Array (Bool × α))] : RamInput (Array (Option α)) :=
  comap (Representation.optionEmbedding (default : α)).arrayMap

instance arrayOptionProd {α : Type u} {β : Type v} [Inhabited α]
    [Input (Array (Bool × α) × β)] [RamInput (Array (Bool × α) × β)] :
    RamInput (Array (Option α) × β) :=
  comap ((Representation.optionEmbedding (default : α)).arrayMap.prodMap
    (Function.Embedding.refl β))

end Complexity.Program.RamInput
