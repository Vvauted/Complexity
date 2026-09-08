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
import Complexity.Tactic.Ram.Source

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
  ram_total_start input entry ⟨rfl, represented⟩
  ram_total_init functions.function.lowerBound at initial with bindings
  refine Verification.TotalWP.mono_post
    (loop_total (functionRegisters ?layout) (base := array.base) (key := key)
      (original := initial) hw sorted _ ?initialInvariant) ?post
  case layout => decide
  case initialInvariant =>
    apply Pre.invariant
    · exact ⟨represented.2, bindings.xs.base, bindings.key,
        by simpa only [bindings.hi] using represented.1⟩
    · exact bindings.lo
  case post =>
    intro finish post
    have shared : entry.restore finish = entry :=
      State.restore_eq_of_shared post.mem post.input post.output
    ram_total_vc [functions.result_eq.lowerBound]
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
  ram_time_start args entry ⟨rfl, represented⟩
  ram_time_init functions.function.lowerBound at initial with bindings
  refine (loop_timeBound (functionRegisters ?layout) (base := array.base) (key := key)
    hw sorted initial).consequence ?initialInvariant ?reserve
  case layout => decide
  case initialInvariant =>
    rintro s rfl
    apply Pre.invariant
    · exact ⟨represented.2, bindings.xs.base, bindings.key,
        by simpa only [bindings.hi] using represented.1⟩
    · exact bindings.lo
  case reserve =>
    rintro s rfl
    ram_simp [functionRegisters, bindings.lo, bindings.hi,
      initial.lo, initial.hi, represented.1, Nat.mul_comm]

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
