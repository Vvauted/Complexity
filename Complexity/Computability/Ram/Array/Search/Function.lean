/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Search.Time
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Computability.Ram.Source.State.Frame
import Complexity.Computability.Ram.Verification.Function.Typed
import Complexity.Computability.Ram.Verification.Time.Function
import Complexity.Tactic.Ram.Total
import Complexity.Tactic.Ram.Time

/-!
# A callable lower-bound search

`functions` declares a function over an existing array reference and a key.
It returns the insertion position as a word, including the array length when
all elements are smaller. The two interval endpoints and midpoint are ordinary
source locals. The array is borrowed; neither a loader nor stream I/O is part
of this invocation.
-/

namespace Ram.Source.Array.Search

/-- Search a sorted represented array using unsigned comparisons. The midpoint
uses the difference of the endpoints rather than their potentially overflowing sum. -/
ram_def functions := ram_functions% {
  fn lowerBound(xs : array, key) {
    let mut lo := 0;
    let mut hi := xs.length;
    while lo < hi {
      let mid := lo + (hi - lo) / 2;
      if xs[mid] < key {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    return lo;
  }
}

private def functionRegisters {lo hi mid : Reg}
    (distinct : [0, 1, 2, lo, hi, mid].Nodup) : Registers := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at distinct
  exact
    { base := 0
      key := 2
      lo := lo
      hi := hi
      mid := mid
      base_ne_lo := distinct.1.2.2.1
      base_ne_hi := distinct.1.2.2.2.1
      base_ne_mid := distinct.1.2.2.2.2
      key_ne_lo := distinct.2.2.1.1
      key_ne_hi := distinct.2.2.1.2.1
      key_ne_mid := distinct.2.2.1.2.2
      lo_ne_hi := distinct.2.2.2.1.1
      lo_ne_mid := distinct.2.2.2.1.2
      hi_ne_mid := distinct.2.2.2.2 }

private def functionStart (lo hi : Reg) (array : ArrayRef w) (key : Word w)
    (entry : State w) : State w :=
  ((entry.enter (array.args ++ [key])).setReg lo 0).setReg hi array.length

private theorem functionStart_invariant {lo hi mid heapLimit : Nat}
    {array : ArrayRef w} {key : Word w} {xs : List (Word w)} {entry : State w}
    (distinct : [0, 1, 2, lo, hi, mid].Nodup)
    (represented : array.Rep heapLimit xs entry) :
    Invariant (functionRegisters distinct) heapLimit array.base key xs
      (functionStart lo hi array key entry) (functionStart lo hi array key entry) := by
  let registers := functionRegisters distinct
  have baseLo : (0 : Reg) ≠ lo := registers.base_ne_lo
  have baseHi : (0 : Reg) ≠ hi := registers.base_ne_hi
  have keyLo : (2 : Reg) ≠ lo := registers.key_ne_lo
  have keyHi : (2 : Reg) ≠ hi := registers.key_ne_hi
  have separate : lo ≠ hi := registers.lo_ne_hi
  refine ⟨represented.2, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · change (functionStart lo hi array key entry).regs 0 = array.base
    simp [functionStart, State.setReg, State.enter, ArrayRef.args, baseHi, baseLo]
  · change (functionStart lo hi array key entry).regs 2 = key
    simp [functionStart, State.setReg, State.enter, ArrayRef.args, keyHi, keyLo]
  · change ((functionStart lo hi array key entry).regs lo).toNat ≤
      ((functionStart lo hi array key entry).regs hi).toNat
    simp [functionStart, State.setReg, separate]
  · change ((functionStart lo hi array key entry).regs hi).toNat ≤ xs.length
    simpa only [functionStart, State.setReg_same] using represented.1.le
  · intro i inside lower
    change i < ((functionStart lo hi array key entry).regs lo).toNat at lower
    simp [functionStart, State.setReg, separate] at lower
  · intro i inside lower
    change ((functionStart lo hi array key entry).regs hi).toNat ≤ i at lower
    simp only [functionStart, State.setReg_same, represented.1] at lower
    omega
  · intro r _ _ _
    rfl

/-- The named function returns the ordinary lower-bound position and preserves
the entire caller state. Sortedness and represented data suffice; there is no
instruction budget or extra strict array-endpoint condition. -/
theorem function_contract {w heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {key : Word w} {xs : List (Word w)}
    (hw : 2 ≤ w) (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    TypedFunctionContract program heapLimit depth functions.function.lowerBound .word
      (fun input : ArrayRef w × Word w => functions.arguments.lowerBound input.1 input.2)
      (fun input entry => input = (array, key) ∧ array.Rep heapLimit xs entry)
      (fun _ entry value finish => LowerBoundSpec xs key value.toNat ∧ finish = entry) := by
  ram_total_vc input entry ⟨rfl, represented⟩
    [functions.body_eq.lowerBound, functions.result_eq.lowerBound]
  refine Verification.TotalWP.mono_post
    (loop_total (functionRegisters ?layout) (base := array.base) (key := key)
      (original := functionStart functions.localReg.lowerBound.lo
        functions.localReg.lowerBound.hi array key entry) hw sorted _ ?initial) ?post
  case layout => decide
  case initial => exact functionStart_invariant (by decide) represented
  case post =>
    intro finish post
    have shared : entry.restore finish = entry :=
      State.restore_eq_of_shared post.mem post.input post.output
    exact ⟨post.result, shared⟩

/-- The same callable body has a logarithmic compiled time bound. This theorem
is independent of its budget-free correctness proof; the enclosing call, return
and halt are charged separately by the executable function interface. -/
theorem function_timeBound {w control heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {key : Word w} {xs : List (Word w)}
    (hw : 2 ≤ w) (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    FunctionTimeBound control program heapLimit depth functions.function.lowerBound
      (fun args entry => args = functions.arguments.lowerBound array key ∧
        array.Rep heapLimit xs entry)
      (fun _ _ => 25 * Nat.clog 2 (xs.length + 1) + 8) := by
  ram_time_vc args entry ⟨rfl, represented⟩ [functions.body_eq.lowerBound]
  refine (loop_timeBound (functionRegisters ?layout) (base := array.base) (key := key)
    hw sorted (functionStart functions.localReg.lowerBound.lo
      functions.localReg.lowerBound.hi array key entry)).consequence ?initial ?reserve
  case layout => decide
  case initial =>
    rintro s rfl
    exact functionStart_invariant (by decide) represented
  case reserve =>
    rintro s rfl
    change Nat.clog 2 (array.length.toNat + 1) * 25 + 4 ≤ _
    simp [represented.1, Nat.mul_comm]

/-- The semantic observation returns the standard list insertion index, with
no independently implemented reference algorithm. Its shared state is unchanged. -/
theorem eval_eq {w heapLimit : Nat} {array : ArrayRef w} {key : Word w}
    {xs : List (Word w)} {entry : State w}
    (hw : 2 ≤ w) (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat))
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.lowerBound array key heapLimit entry =
      Part.some (BitVec.ofNat w (xs.findIdx (fun x => decide (key.toNat ≤ x.toNat))), entry) := by
  obtain ⟨value, finish, execution, result, rfl⟩ :=
    function_contract (program := functions.program) (depth := 0) hw sorted
      (array, key) entry ⟨rfl, represented⟩
  have index : value = BitVec.ofNat w
      (xs.findIdx (fun x => decide (key.toNat ≤ x.toNat))) := by
    rw [← result.eq_findIdx]
    exact (Word.ofNat_toNat_self value).symm
  simpa only [index] using execution.evalTyped_eq_some functions.results_length.lowerBound

end Ram.Source.Array.Search
