/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Std.Do.Triple.Basic

/-!
# Consequence for native monadic specifications

Reuse a native `Std.Do.Triple` with a stronger precondition and a weaker
postcondition. This is the consequence rule of the existing predicate
transformer, for any supported monad and postcondition shape. In particular,
`Triple.and` can first combine separate properties of the same computation;
`Triple.mono` then expresses their mathematical consequence without exposing
the computation's execution witnesses or unfolding its weakest precondition.
-/

namespace Std.Do.Triple

universe u v

variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
variable {α : Type u} {action : m α} {pre pre' : Assertion ps}
variable {post post' : PostCond α ps}

/-- Strengthen a native specification's precondition and weaken its
postcondition, including every exceptional outcome in its postcondition shape.
The action and its weakest-precondition interpretation are unchanged. -/
theorem mono (specification : Triple action pre post)
    (precondition : SPred.entails pre' pre) (postcondition : PostCond.entails post post') :
    Triple action pre' post' :=
  SPred.entails.trans precondition
    (SPred.entails.trans specification ((WP.wp action).mono _ _ postcondition))

end Std.Do.Triple
