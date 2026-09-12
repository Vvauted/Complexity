/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Frame
import Complexity.Computability.Ram.Compiler.Language.Placement
import Complexity.Computability.Ram.Compiler.Language.Control
import Complexity.Computability.Ram.Compiler.Language.Heap.Node
import Complexity.Language.Rooted.Execution

/-!
# The common postcondition for allocating core compilation

This predicate packages the existing measured RAM execution and typed lexical
correspondence. It is not another evaluator. The supplied source execution fixes
the actual final heap and control outcome; a successful simulation additionally
returns the final placement and shared allocation cursor.

Agreement on every original object protects suspended caller descriptors.
Conditional final-local matching is retained even on return, so an effectful
Boolean guard can feed its actual updated locals to the enclosing loop.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A source execution has the given counted implementation at every legal
local layout. The selected cursor and word/call capacities are backend data;
the source execution does not depend on an instruction budget. -/
def ArenaCoreSimulates {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {Γ : List Ty} {result : Ty}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {outcome : Control result}
    (_execution : Complexity.Language.Exec program stmt entry finish outcome)
    (w heapLimit depth cursor finalCursor steps : Nat) : Prop :=
  ∀ (controlReg : Nat), 0 < w → ∀ (placement : Nat → Word w)
    (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
    RegisterMap.Regular layout → layout.Bounded next →
    layout.Matches placement entry.locals s.regs → layout.Avoids flag →
    flag < next → resultSlot + fieldCount result ≤ flag →
    (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
    entry.locals.Rooted entry.heap → ArenaRep placement cursor heapLimit entry.heap s →
    s.regs flag = 0 →
    ∃ finalPlacement t,
      Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) steps s t ∧
      ControlMatches layout finalPlacement resultSlot flag finish.locals outcome t ∧
      ArenaRep finalPlacement finalCursor heapLimit finish.heap t ∧
      Placement.Agrees entry.heap placement finalPlacement ∧
      (layout.AvoidsRange resultSlot (fieldCount result) →
        layout.Matches finalPlacement finish.locals t.regs)

namespace ArenaCoreSimulates

/-- Fresh lexical fields preserve the existing sequential-copy precondition. -/
theorem copySafe_extend {Γ : List Ty} {layout : RegisterMap Γ} {result τ : Ty}
    {resultSlot next : Reg}
    (safe : fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result))
    (fresh : resultSlot + fieldCount result ≤ next) :
    fieldCount result ≤ 1 ∨
      RegisterMap.AvoidsRange (RegisterMap.extend layout τ next)
        resultSlot (fieldCount result) := by
  rcases safe with single | separate
  · exact Or.inl single
  · exact Or.inr (separate.extend fresh)

end ArenaCoreSimulates
end Ram.LanguageCompiler
