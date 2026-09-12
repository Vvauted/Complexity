/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Verification
import Complexity.Language.Rooted.Execution

/-!
# Heap preservation supplied by source function contracts

Every actual source execution preserves old object identities, extents and
immutable node fields. A function contract therefore carries these facts
without asking its author to repeat them. Mutable buffer contents may change;
this is not an unchanged-heap or no-aliasing premise.

The strengthened postcondition concerns the same returned value and heap as
the supplied contract. It adds neither a resource budget nor another execution.
-/

namespace Complexity.Language.FunctionTotal

/-- Retain the original postcondition together with the old-object preservation
already guaranteed by the same actual source execution. -/
theorem with_heap_shapeExtends {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (correct : FunctionTotal program fn pre post) :
    FunctionTotal program fn pre (fun args initial value finish =>
      post args initial value finish ∧ initial.ShapeExtends finish) := by
  intro args heap input
  obtain ⟨finish, value, execution, property⟩ := correct args heap input
  exact ⟨finish, value, execution, property, execution.heap_shapeExtends⟩

end Complexity.Language.FunctionTotal
