/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Complexity.Computability.Ram.Array.Sum
import Examples.Ram.ArraySum

/-!
# Computing a graph degree from a represented adjacency row

The executable function is `Ram.Source.Array.sumFunctions.function.sum`: the
same fixed array loop used for ordinary word sums. Its specification here uses
mathlib's `SimpleGraph` and `SimpleGraph.degree`, without opening that loop's
register, call-frame or memory-preservation proofs.

The adjacency row must already be present in memory. `adjacencyRow` describes
that representation; it is not an executable graph loader or a free call to a
Lean adjacency predicate. The function receives only a pointer and a length.
The address bound ensures both safe traversal and an exact, non-wrapping degree.
Correctness uses no proposed step budget. The separate time theorem bounds the
same function body; an enclosing call additionally pays its generated overhead.
-/

namespace Ram.Examples.GraphDegree

open Source Source.Array

variable {n w : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

/-- The mathematical view of one preloaded adjacency row, with one word per
vertex. This definition specifies memory contents; the RAM function does not
evaluate `G.Adj`. -/
def adjacencyRow (w : Nat) : List (Word w) :=
  List.ofFn fun u : Fin n => if G.Adj v u then 1 else 0

@[simp] theorem length_adjacencyRow : (adjacencyRow G v w).length = n := by
  simp [adjacencyRow]

/-- Reinterpret the list sum using mathlib's finite-neighbor-set definition
of degree. No implementation-specific invariant is needed in this step. -/
theorem sum_adjacencyRow_toNat (hw : 0 < w) :
    ((adjacencyRow G v w).map BitVec.toNat).sum = G.degree v := by
  calc
    ((adjacencyRow G v w).map BitVec.toNat).sum =
        ∑ u : Fin n, if G.Adj v u then 1 else 0 := by
      rw [adjacencyRow, List.map_ofFn, Fin.sum_ofFn]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : G.Adj v u <;> simp [h, BitVec.toNat_one hw]
    _ = G.degree v := by
      simp only [Finset.sum_boole, SimpleGraph.degree, G.neighborFinset_eq_filter,
        Nat.cast_id]

/-- The returned word decodes to the exact mathematical degree when the row
length fits; the graph-theoretic bound comes directly from mathlib. -/
theorem wordSum_adjacencyRow_toNat (hw : 0 < w) (hfit : n < 2 ^ w) :
    (wordSum (adjacencyRow G v w)).toNat = G.degree v := by
  rw [wordSum_toNat, sum_adjacencyRow_toNat G v hw, Nat.mod_eq_of_lt]
  exact lt_trans (by simpa using G.degree_lt_card_verts v) hfit

/-- A graph-valued mathematical specification of the reusable sum function.
Only its parameter list, represented input row and returned value are visible;
the entire caller state is preserved. -/
theorem function_contract {program : Program} {heapLimit depth : Nat} {base : Word w}
    (hw : 0 < w) (hfit : base.toNat + n < 2 ^ w) :
    FunctionContract program heapLimit depth sumFunctions.function.sum
      (fun args entry =>
        args = sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩ ∧
        ArrayAt heapLimit base (adjacencyRow G v w) entry)
      (fun _ entry values finish =>
        ∃ value, values = [value] ∧ value.toNat = G.degree v ∧ finish = entry) := by
  apply (sum_function_contract (program := program) (depth := depth)
    (base := base) (xs := adjacencyRow G v w) hw (by simpa using hfit)).consequence
  · intro args entry pre
    simpa only [length_adjacencyRow] using pre
  · rintro args entry value finish _ ⟨rfl, same⟩
    exact ⟨wordSum (adjacencyRow G v w), rfl,
      wordSum_adjacencyRow_toNat G v hw (by omega), same⟩

/-- Compute a graph degree without a `main`, an input stream or an output
instruction. This is an invocation of the actual fixed array-sum function. -/
theorem function_runs {program : Program} {heapLimit depth : Nat} {base : Word w}
    (hw : 0 < w) (hfit : base.toNat + n < 2 ^ w) (entry : Source.State w)
    (represented : ArrayAt heapLimit base (adjacencyRow G v w) entry) :
    ∃ value,
      FunctionExec program heapLimit depth sumFunctions.function.sum
        (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩) entry [value] entry ∧
      value.toNat = G.degree v := by
  obtain ⟨values, finish, execution, value, rfl, correct, rfl⟩ :=
    function_contract G v (program := program) (depth := depth) hw hfit
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩) entry ⟨rfl, represented⟩
  exact ⟨value, execution, correct⟩

/-- The unchanged implementation has a linear body-step bound in the number
of vertices. Constructing the represented row and invoking the function from
another function are not included in this body count. -/
theorem function_timeBound {program : Program} {control heapLimit depth : Nat}
    {base : Word w} (hw : 0 < w) (hfit : base.toNat + n < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth sumFunctions.function.sum
      (fun args entry =>
        args = sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩ ∧
        ArrayAt heapLimit base (adjacencyRow G v w) entry)
      (fun _ _ => 18 * n + 8) := by
  simpa only [length_adjacencyRow] using
    (sum_function_timeBound (control := control) (program := program) (depth := depth)
      (base := base) (xs := adjacencyRow G v w) hw (by simpa using hfit))

/-- Correctness and cost hold of one invocation, rather than unrelated
mathematical result and time functions. -/
theorem function_runs_with_timeBound {program : Program} {control heapLimit depth : Nat}
    {base : Word w} (hw : 0 < w) (hfit : base.toNat + n < 2 ^ w) (entry : Source.State w)
    (represented : ArrayAt heapLimit base (adjacencyRow G v w) entry) :
    ∃ bodySteps value,
      FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
        (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩) bodySteps entry [value] entry ∧
      value.toNat = G.degree v ∧ bodySteps ≤ 18 * n + 8 := by
  obtain ⟨bodySteps, values, finish, execution, ⟨value, rfl, correct, rfl⟩, bound⟩ :=
    (function_contract G v (program := program) (depth := depth) hw hfit).with_timeBound
      (function_timeBound G v (control := control) hw hfit)
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w n⟩) entry ⟨rfl, represented⟩
  exact ⟨bodySteps, value, execution, correct, bound⟩

/-- The ordinary executable sum returns a graph degree on a represented
adjacency row. The proof uses its value equation and mathlib's graph facts;
it does not reopen an execution relation, loop or calling convention. -/
theorem sum_eq_degree {heapLimit : Nat} {array : ArrayRef 32}
    {entry : Source.State 32}
    (fit : array.base.toNat + n < 2 ^ 32)
    (hstack : heapLimit + ABI.frameSize sumFunctions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit (adjacencyRow G v 32) entry) :
    ArraySum.sum array heapLimit entry
      ⟨adjacencyRow G v 32, represented, by simpa using fit⟩ hstack = G.degree v := by
  rw [ArraySum.sum_eq (by simpa using fit) hstack represented,
    sum_adjacencyRow_toNat G v (by decide : 0 < 32)]
  exact Nat.mod_eq_of_lt (lt_trans (by simpa using G.degree_lt_card_verts v) (by omega))

end Ram.Examples.GraphDegree
