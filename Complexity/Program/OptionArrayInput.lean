/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.IntInput
import Complexity.Language.Representation.Array.Option

/-!
# Fixed optional-element array interfaces

The presence column distinguishes `none` from `some default`. Payload columns
retain their existing fixed representation and canonical default at absent
positions. These are preloaded input and final-heap observations, not free
packing, decoding or source array operations.
-/

namespace Complexity.Program

open Language

universe u v

namespace Input

instance arrayOption {α : Type u} [Inhabited α] [Input (Array (Bool × α))] :
    Input (Array (Option α)) :=
  comap inferInstance (Representation.optionEmbedding (default : α)).arrayMap

instance arrayOptionProd {α : Type u} {β : Type v} [Inhabited α]
    [Input (Array (Bool × α) × β)] : Input (Array (Option α) × β) :=
  comap inferInstance ((Representation.optionEmbedding (default : α)).arrayMap.prodMap
    (Function.Embedding.refl β))

namespace PrefixClosed

instance arrayOption {α : Type u} [Inhabited α] [Input (Array (Bool × α))]
    [PrefixClosed (Array (Bool × α))] : PrefixClosed (Array (Option α)) :=
  comap inferInstance (Representation.optionEmbedding (default : α)).arrayMap

instance arrayOptionProd {α : Type u} {β : Type v} [Inhabited α]
    [Input (Array (Bool × α) × β)] [PrefixClosed (Array (Bool × α) × β)] :
    PrefixClosed (Array (Option α) × β) :=
  comap inferInstance ((Representation.optionEmbedding (default : α)).arrayMap.prodMap
    (Function.Embedding.refl β))

end PrefixClosed
end Input

namespace Output

/-- Both columns observe every element at the same actual final heap. -/
instance arrayOption {α : Type u} [Inhabited α] [Output (Array α)] :
    Output (Array (Option α)) where
  type := .prod (.buffer .bool) (Output.type (Array α))
  representation := Representation.arrayOption default (Output.representation (β := Array α))

end Output
end Complexity.Program
