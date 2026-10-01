/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Input
import Complexity.Language.Representation.List.Int

/-!
# Fixed linked output layouts

Pair lists compose their existing field-list observations at the return heap.
Integer lists reuse the canonical constructor view and real Boolean/natural
chains. These instances fix output observations; they do not preload list
inputs, implement source operations, or certify their execution costs.
-/

namespace Complexity.Program.Output

open Language

universe u v

/-- Observe an ordinary list of pairs through its synchronized field chains. -/
instance listProd {α : Type u} {β : Type v} [Output (List α)] [Output (List β)] :
    Output (List (α × β)) where
  type := .prod (Output.type (List α)) (Output.type (List β))
  representation := Representation.listProd
    (Output.representation (β := List α)) (Output.representation (β := List β))

/-- Observe the complete signed list through both actual linked field chains. -/
instance listInt : Output (List Int) where
  type := .prod (.option (.node .bool)) (.option (.node .nat))
  representation := Representation.listInt

end Complexity.Program.Output
