/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Program
import Examples.Language.Splay.Search
import Complexity.Language.Heap.Tree
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Compiler-derived costs of the splay implementation

The bounds below concern the existing `ExecutionCost` of the declared source
program and its actual lowering. In particular, rotation charges count the
two field reads, two field writes, control dispatch and function initialization.
They are not prices assigned to mathematical tree rotations.

Functional correctness and source termination remain independent of these
conditional bounds. A completed realized execution supplies the successful
accesses; its instruction accounting does not ask for a second safety proof.
-/

namespace Complexity.Language.Examples.Splay

open Ram.LanguageCompiler

/-- The complete rotation body bound, from two compiled reads, two compiled
writes, two sequence dispatches, a scalar return and flag initialization. -/
def rotationBodyBound : Nat := 2 * readCodeSize + 2 * writeCodeSize + 10

/-- The actual right-rotation function obeys its compiler-derived bound at
every successful represented invocation; no content-dependent bound is needed. -/
theorem rotateRight_costBound :
    FunctionCostBound Implementation.program Implementation.rotateRightId
      (fun _ _ => True) (fun _ _ => rotationBodyBound) := by
  ram_source_cost (left right root)
  all_goals norm_num [rotationBodyBound, readCodeSize, writeCodeSize]

/-- The independently lowered left rotation has the same body bound. Its
behavioral symmetry is not used as a substitute for instruction accounting. -/
theorem rotateLeft_costBound :
    FunctionCostBound Implementation.program Implementation.rotateLeftId
      (fun _ _ => True) (fun _ _ => rotationBodyBound) := by
  ram_source_cost (left right root)
  all_goals norm_num [rotationBodyBound, readCodeSize, writeCodeSize]

/-- Either rotation call pays its actual generated argument/frame/return work
in addition to the verified body bound. -/
def rotationCallBound : Nat :=
  max (callCost Implementation.program Implementation.rotateRightId rotationBodyBound)
    (callCost Implementation.program Implementation.rotateLeftId rotationBodyBound)

/-- The pure mathematical tree determines the initial root and search query;
its representation records the actual values read before the recursive call. -/
def splayCostPre (key : Nat → Nat) (query : Nat) (tree : Tree Nat)
    : Env Implementation.signatures[Implementation.splayId].params → Heap → Prop :=
  Implementation.splay_onArgs fun keys left right currentRoot currentQuery heap =>
    currentRoot = BufferTree.root tree ∧ currentQuery = query ∧
      BufferTree.Rep key keys left right heap tree

/-- A conservative per-level coefficient from this program's actual emitted
code and helper calls. Static code length is used only as a sufficient allowance
for the acyclic non-callee work; recursive execution is charged separately. -/
def splayLayerBound : Nat :=
  sourceCodeSize (Ram.LocalCompiler.calleeLocals (lowerProgram Implementation.program))
      Implementation.splayBody +
    callCost Implementation.program Implementation.splayId 0 + 2 * rotationCallBound + 2

/-- The empty-tree branch incurs only the actual test, branch and return work. -/
theorem splay_nil_costBound (key : Nat → Nat) (query : Nat) :
    FunctionCostBound Implementation.program Implementation.splayId
      (splayCostPre key query .nil) (fun _ _ => 13) := by
  ram_source_cost_intro (keys left right currentRoot currentQuery)
  intro heap input
  simp only [splayCostPre, Implementation.splay_onArgs, Env.head_cons, Env.tail_cons] at input
  rcases input with ⟨rootEq, queryEq, _⟩
  subst currentRoot currentQuery
  dsimp only [BufferTree.root]
  apply StmtCostBound.mono
  · ram_source_cost_step
  · norm_num [primCodeSize]

set_option maxRecDepth 2048 in
private theorem local_allowance : 100 ≤
    sourceCodeSize (Ram.LocalCompiler.calleeLocals (lowerProgram Implementation.program))
      Implementation.splayBody := by decide

private theorem layer_allowance : rotationCallBound + 100 ≤ splayLayerBound := by
  have available := local_allowance
  unfold splayLayerBound
  omega

private theorem recursive_layer_le {smaller whole : Nat} (progress : smaller + 1 ≤ whole) :
    splayLayerBound * (smaller + 1) + 2 +
        callCost Implementation.program Implementation.splayId 0 +
        2 * rotationCallBound + 100 ≤ splayLayerBound * (whole + 1) := by
  have scaled := Nat.mul_le_mul_left splayLayerBound progress
  have available := local_allowance
  have allowance : 2 + callCost Implementation.program Implementation.splayId 0 +
      2 * rotationCallBound + 100 ≤ splayLayerBound := by
    unfold splayLayerBound
    omega
  simp only [Nat.mul_add, Nat.mul_one] at scaled ⊢
  omega

set_option maxHeartbeats 400000 in
/-- The real compiled splay body costs at most a fixed compiler-derived amount
per traversed search edge, plus one initial allowance. The ghost search path
counts only nonempty child edges; even a final recursive call on zero is paid.

The proof uses the represented reads only to select the source branch and the
actual recursive child. It does not require BST order, distinct identifiers,
heap frames or a second functional-correctness proof: those belong to the
independent source contract. All bounds remain conditional on actual successful
realized execution, uniformly in word width and permitted call nesting. -/
theorem splay_costBound_at (key : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    FunctionCostBound Implementation.program Implementation.splayId
      (splayCostPre key query tree)
      (fun _ _ => splayLayerBound * (searchDepth key query tree + 1) + 2) := by
  have allTrees : ∀ n (tree : Tree Nat), tree.numNodes = n →
      FunctionCostBound Implementation.program Implementation.splayId
        (splayCostPre key query tree)
        (fun _ _ => splayLayerBound * (searchDepth key query tree + 1) + 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro tree size
      cases tree with
      | nil =>
        apply (splay_nil_costBound key query).mono_bound
        intro args heap input
        have available := layer_allowance
        simp only [searchDepth_nil, Nat.zero_add, Nat.mul_one]
        omega
      | node root a b =>
        ram_source_cost_intro (keys left right currentRoot currentQuery)
        intro heap input
        simp only [splayCostPre, Implementation.splay_onArgs, Env.head_cons, Env.tail_cons] at input
        rcases input with ⟨rootEq, queryEq, represented⟩
        subst currentRoot currentQuery
        rcases BufferTree.Rep.node_iff.mp represented with
          ⟨nonzero, readKey, readLeft, readRight, repA, repB⟩
        have available := layer_allowance
        have rightRotation := Nat.le_max_left
          (callCost Implementation.program Implementation.rotateRightId rotationBodyBound)
          (callCost Implementation.program Implementation.rotateLeftId rotationBodyBound)
        have leftRotation := Nat.le_max_right
          (callCost Implementation.program Implementation.rotateRightId rotationBodyBound)
          (callCost Implementation.program Implementation.rotateLeftId rotationBodyBound)
        change _ ≤ rotationCallBound at rightRotation leftRotation
        norm_num only [rotationBodyBound, readCodeSize, writeCodeSize] at rightRotation leftRotation
        have initialAllowance : splayLayerBound ≤
            splayLayerBound * (searchDepth key query (.node root a b) + 1) := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left splayLayerBound
            (show 1 ≤ searchDepth key query (.node root a b) + 1 by omega)
        dsimp only [BufferTree.root]
        apply Classical.byCases (p := query < key root)
        · intro toLeft
          cases a with
          | nil =>
            simp only [BufferTree.root] at readLeft
            apply StmtCostBound.mono
            · ram_source_cost_step
            · norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount]
              omega
          | node child x y =>
            rcases BufferTree.Rep.node_iff.mp repA with
              ⟨childNonzero, readChildKey, readChildLeft, readChildRight, repX, repY⟩
            simp only [BufferTree.root] at readLeft
            apply Classical.byCases (p := query < key child)
            · intro toLeftLeft
              have smaller : x.numNodes < n := by simp only [Tree.numNodes] at size; omega
              have recursive := ih x.numNodes smaller x rfl
              have progress : searchDepth key query x + 1 ≤
                  searchDepth key query (.node root (.node child x y) b) := by
                cases x <;> simp [searchDepth, toLeft, toLeftLeft]
              have budget := recursive_layer_le progress
              apply StmtCostBound.mono
              · ram_source_cost_step using [recursive, rotateRight_costBound]
                all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                  Env.head_cons, Env.tail_cons,
                  Except.ok.injEq, and_self]
              · rw [callCost_eq_add]
                norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                  rotationBodyBound]
                omega
            · intro toLeftLeft
              apply Classical.byCases (p := key child < query)
              · intro toLeftRight
                have smaller : y.numNodes < n := by simp only [Tree.numNodes] at size; omega
                have recursive := ih y.numNodes smaller y rfl
                have progress : searchDepth key query y + 1 ≤
                    searchDepth key query (.node root (.node child x y) b) := by
                  cases y <;> simp [searchDepth, toLeft, toLeftLeft, toLeftRight]
                have budget := recursive_layer_le progress
                apply StmtCostBound.mono
                · ram_source_cost_step using [recursive, rotateRight_costBound, rotateLeft_costBound]
                  all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                    Env.head_cons, Env.tail_cons,
                    Except.ok.injEq, and_self]
                · rw [callCost_eq_add]
                  norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                    rotationBodyBound]
                  omega
              · intro toLeftRight
                apply StmtCostBound.mono
                · ram_source_cost_step using rotateRight_costBound
                  all_goals trivial
                · norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                    rotationBodyBound]
                  omega
        · intro toLeft
          apply Classical.byCases (p := key root < query)
          · intro toRight
            cases b with
            | nil =>
              simp only [BufferTree.root] at readRight
              apply StmtCostBound.mono
              · ram_source_cost_step
              · norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount]
                omega
            | node child x y =>
              rcases BufferTree.Rep.node_iff.mp repB with
                ⟨childNonzero, readChildKey, readChildLeft, readChildRight, repX, repY⟩
              simp only [BufferTree.root] at readRight
              apply Classical.byCases (p := key child < query)
              · intro toRightRight
                have smaller : y.numNodes < n := by simp only [Tree.numNodes] at size; omega
                have recursive := ih y.numNodes smaller y rfl
                have progress : searchDepth key query y + 1 ≤
                    searchDepth key query (.node root a (.node child x y)) := by
                  cases y <;> simp [searchDepth, toLeft, toRight,
                    Nat.not_lt_of_ge (Nat.le_of_lt toRightRight), toRightRight]
                have budget := recursive_layer_le progress
                apply StmtCostBound.mono
                · ram_source_cost_step using [recursive, rotateLeft_costBound]
                  all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                    Env.head_cons, Env.tail_cons,
                    Except.ok.injEq, and_self]
                · rw [callCost_eq_add]
                  norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                    rotationBodyBound]
                  omega
              · intro toRightRight
                apply Classical.byCases (p := query < key child)
                · intro toRightLeft
                  have smaller : x.numNodes < n := by simp only [Tree.numNodes] at size; omega
                  have recursive := ih x.numNodes smaller x rfl
                  have progress : searchDepth key query x + 1 ≤
                      searchDepth key query (.node root a (.node child x y)) := by
                    cases x <;> simp [searchDepth, toLeft, toRight, toRightLeft]
                  have budget := recursive_layer_le progress
                  apply StmtCostBound.mono
                  · ram_source_cost_step using [recursive, rotateRight_costBound, rotateLeft_costBound]
                    all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                      Env.head_cons, Env.tail_cons,
                      Except.ok.injEq, and_self]
                  · rw [callCost_eq_add]
                    norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                      rotationBodyBound]
                    omega
                · intro toRightLeft
                  apply StmtCostBound.mono
                  · ram_source_cost_step using rotateLeft_costBound
                    all_goals trivial
                  · norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount,
                      rotationBodyBound]
                    omega
          · intro toRight
            apply StmtCostBound.mono
            · ram_source_cost_step
            · norm_num only [primCodeSize, readCodeSize, writeCodeSize, fieldCount]
              omega
  exact allTrees tree.numNodes tree rfl

end Complexity.Language.Examples.Splay
