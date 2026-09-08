/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Map.Basic
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Verification.Time.ForIn
import Complexity.Computability.Ram.Verification.Time.Function
import Complexity.Computability.Ram.Verification.Time.StraightLine

/-!
# Separate uniform time bounds for in-place map

The helper's conditional function bound pays for its actual body. The call
rule adds argument evaluation, frame work, return expressions and receipt of
the returned word. The map body then executes its indexed store and generated
index increment; the shared foreach rule counts loads, cursor writes and guards.

These bounds require neither helper totality nor a mathematical mapping
specification. Completed execution supplies safety, and the actual call restores
the loop's remaining-count register independently of the helper's heap effects.
The function bound concerns body work, not its own enclosing invocation or halt.
-/

namespace Ram.Source.Array.Map

variable {w control fn heapLimit depth bodyBudget : Nat} {program : Program} {helper : Func}

/-- The indexed store costs five instructions and the explicit index increment
costs four, in addition to the actual helper call and its returned-field receipt. -/
theorem body_timeBound (lookup : program[fn]? = some helper)
    (time : FunctionTimeBound (w := w) control program heapLimit depth helper
      (fun args _ => args.length = 1) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1) (body fn)
      (fun _ => True)
      (fun _ => ((ABI.callPrefixLocals control helper.locals [.var 5] 0).length + 1 +
        bodyBudget + (ABI.returnCodeResultsLocals control helper.locals helper.results).length +
        1) + 9) := by
  apply TimeBound.seq_const (time.call (dsts := [6]) (args := [.var 5])
    (R := fun _ => True) lookup (fun _ _ => by simp))
  exact TimeBound.of_isStraightLine (by simp [Stmt.IsStraightLine])

/-- A completed map traversal pays for the helper call plus twenty-three
instructions per item, and eight setup/final-guard instructions. This conditional
bound does not require represented array contents or helper termination. -/
theorem code_timeBound (hw : 0 < w) (lookup : program[fn]? = some helper)
    (time : FunctionTimeBound (w := w) control program heapLimit depth helper
      (fun args _ => args.length = 1) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1) (code fn)
      (fun _ => True)
      (fun s => (((ABI.callPrefixLocals control helper.locals [.var 5] 0).length + 1 +
        bodyBudget + (ABI.returnCodeResultsLocals control helper.locals helper.results).length +
        1) + 23) * (s.regs 1).toNat + 8) := by
  let callCost := (ABI.callPrefixLocals control helper.locals [.var 5] 0).length + 1 +
    bodyBudget + (ABI.returnCodeResultsLocals control helper.locals helper.results).length + 1
  have traversal := TimeBound.forIn 3 4 5 (base := .var 0) (length := .var 1)
    hw (by decide) (by decide) body_remaining (body_timeBound lookup time)
  intro s _
  have atState : TimeBound control program heapLimit (depth + 1) (code fn)
      (fun current => current = s)
      (fun _ => (callCost + 23) * (s.regs 1).toNat + 8) := by
    apply TimeBound.assign_seq_at
    · change 2 ≤ (callCost + 23) * (s.regs 1).toNat + 8
      omega
    · apply traversal.consequence (fun _ _ => trivial)
      rintro current rfl
      change 1 + 1 + (callCost + 9 + 14) * (s.regs 1).toNat + 4 ≤
        (callCost + 23) * (s.regs 1).toNat + 8 - 2
      have coefficient : callCost + 9 + 14 = callCost + 23 := by omega
      rw [coefficient]
      omega
  exact atState s rfl

/-- Lift the same code bound through the map function's actual two argument
fields. Only the descriptor is fixed: safety and array contents are not premises
of this conditional time bound, and the helper need not be total. -/
theorem function_timeBound (hw : 0 < w) (lookup : program[fn]? = some helper)
    (time : FunctionTimeBound (w := w) control program heapLimit depth helper
      (fun args _ => args.length = 1) (fun _ _ => bodyBudget)) (array : ArrayRef w) :
    FunctionTimeBound (w := w) control program heapLimit (depth + 1) (function fn)
      (fun args _ => args = array.args)
      (fun _ _ => (((ABI.callPrefixLocals control helper.locals [.var 5] 0).length + 1 +
        bodyBudget + (ABI.returnCodeResultsLocals control helper.locals helper.results).length +
        1) + 23) * array.length.toNat + 8) := by
  apply FunctionTimeBound.of_body (code_timeBound hw lookup time)
  · intro args entry _
    trivial
  · rintro args entry rfl
    exact Nat.le_refl _

end Ram.Source.Array.Map
