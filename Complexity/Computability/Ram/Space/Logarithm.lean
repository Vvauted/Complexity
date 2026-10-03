/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Space.Basic
import Complexity.Computability.Ram.Time.Logarithm

/-! A concrete ceiling-log physical-word budget yields logarithmic space. -/

namespace Ram

theorem UniformSpaceBound.logarithmic {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {a b : Nat}
    (h : UniformSpaceBound code encode admissible size post
      (fun n => a * Nat.clog 2 (n + 1) + b)) :
    UniformSpaceBigO code encode admissible size post Nat.log2 :=
  h.bigO_of_isBigO (Asymptotics.isBigO_log2_of_le_clog (fun _ => Nat.le_refl _))

end Ram
