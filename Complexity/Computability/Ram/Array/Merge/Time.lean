/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Merge.Function
import Complexity.Tactic.Ram.Time

/-!
# Separate time bounds for callable merge

The raw core reuses the existing merge loop's independent instruction bound.
Its two input counts fit words separately; their natural sum need not fit a
word. The typed three-array wrapper executes one actual call to that core.
The generated argument, frame and return blocks account for its extra cost.

Neither theorem requires sorted inputs. Both retain the represented arrays,
destination extent and destination/source disjointness of the existing merge
interface. These are conditional bounds on the same declared functions, not
termination assumptions or an uncharged host-side merge.
-/

namespace Ram.Source.Array.Merge

/-- The raw function retains the existing loop bound and its separate input
count domain. Only the enclosing caller adds argument and frame costs. -/
theorem core_function_timeBound {w control heapLimit depth : Nat} {functions : Program}
    {left right destination : Word w} {xs ys scratch : List (Word w)}
    (hw : 0 < w) (hleftFit : xs.length < 2 ^ w) (hrightFit : ys.length < 2 ^ w)
    (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination (xs.length + ys.length) left xs.length)
    (hdr : ArraysDisjoint destination (xs.length + ys.length) right ys.length) :
    FunctionTimeBound control functions heapLimit depth mergeFunctions.function.mergeCore
      (fun args entry =>
        args = mergeFunctions.arguments.mergeCore left right destination
          (BitVec.ofNat w xs.length) (BitVec.ofNat w ys.length) ∧
        ArrayAt heapLimit left xs entry ∧ ArrayAt heapLimit right ys entry ∧
          ArrayAt heapLimit destination scratch entry)
      (fun _ _ => 34 * (xs.length + ys.length) + 4) := by
  apply FunctionTimeBound.of_body
    (R := Pre heapLimit left right destination xs ys scratch)
    (bodyBound := fun _ => 34 * (xs.length + ys.length) + 4)
  · simpa only [core_body] using
      (timeBound (control := control) (functions := functions)
        (heapLimit := heapLimit) (depth := depth) hw hlen hdl hdr)
  · rintro args entry ⟨rfl, leftArray, rightArray, destinationArray⟩
    exact core_pre hleftFit hrightFit leftArray rightArray destinationArray
  · intro args entry pre
    exact Nat.le_refl _

/-- The typed wrapper's one real call contributes its generated argument,
frame and empty-result return blocks in addition to the core's linear bound.
The enclosing invocation and halt are accounted for separately at runtime. -/
theorem function_timeBound {w control heapLimit depth : Nat}
    {left right destination : ArrayRef w} {xs ys scratch : List (Word w)}
    (hw : 0 < w) (hlen : scratch.length = xs.length + ys.length)
    (hdl : ArraysDisjoint destination.base (xs.length + ys.length) left.base xs.length)
    (hdr : ArraysDisjoint destination.base (xs.length + ys.length) right.base ys.length) :
    FunctionTimeBound control mergeFunctions.program heapLimit (depth + 1)
      mergeFunctions.function.merge
      (fun args entry => args = mergeFunctions.arguments.merge left right destination ∧
        left.Rep heapLimit xs entry ∧ right.Rep heapLimit ys entry ∧
          destination.Rep heapLimit scratch entry)
      (fun _ _ => 34 * (xs.length + ys.length) + 58) := by
  ram_time_vc args entry ⟨rfl, leftArray, rightArray, destinationArray⟩
    [mergeFunctions.body_eq.merge]
  have coreTime := core_function_timeBound
    (control := control) (functions := mergeFunctions.program)
    (heapLimit := heapLimit) (depth := depth)
    hw leftArray.length_lt rightArray.length_lt hlen hdl hdr
  ram_time_call coreTime
    [leftArray.length_eq, rightArray.length_eq, mergeFunctions.result_eq.mergeCore]
  exact ⟨leftArray.2, rightArray.2, destinationArray.2⟩

end Ram.Source.Array.Merge
