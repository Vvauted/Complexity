/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Cost
import Complexity.Computability.Ram.Compiler.Language.DepthTactic

/-!
# Call depth of the declared splay program

The recursive call descends to a grandchild. A rotation does not call any
function, and rotations after the recursive return reuse its released frame.
Consequently the body's sufficient nesting is half the input tree's height,
independently of instruction count. These conditional resource proofs reuse
successful realized executions; they do not repeat source total correctness,
heap framing or the machine simulation.

The outer invocation needs one additional frame. The resulting address envelope
is a stack-capacity bound, not a count of reachable live heap cells.
-/

namespace Complexity.Language.Examples.Splay

open Ram.LanguageCompiler

/-- Internal nesting of the actual splay body. The external trampoline's frame
is accounted for by the shared function invocation interface. -/
def splayDepthBound (tree : Tree Nat) : Nat := tree.height / 2

/-- Rotation helpers do not make calls; their successful reads and writes do
not increase call depth. -/
theorem rotateRight_depthBound :
    FunctionDepthBound Implementation.program Implementation.rotateRightId
      (fun _ _ => True) (fun _ _ => 0) := by
  ram_source_depth_intro (left right root)
  intro heap _
  apply StmtDepthBound.mono
  · ram_source_depth_step
  · simp

/-- The other helper likewise needs no nested call frame. -/
theorem rotateLeft_depthBound :
    FunctionDepthBound Implementation.program Implementation.rotateLeftId
      (fun _ _ => True) (fun _ _ => 0) := by
  ram_source_depth_intro (left right root)
  intro heap _
  apply StmtDepthBound.mono
  · ram_source_depth_step
  · simp

/-- An empty input returns without making a call. -/
theorem splay_nil_depthBound (key : Nat → Nat) (query : Nat) :
    FunctionDepthBound Implementation.program Implementation.splayId
      (splayCostPre key query .nil) (fun _ _ => 0) := by
  ram_source_depth_intro (keys left right currentRoot currentQuery)
  intro heap input
  simp only [splayCostPre, Implementation.splay_onArgs, Env.head_cons, Env.tail_cons] at input
  rcases input with ⟨rootEq, queryEq, _⟩
  subst currentRoot currentQuery
  dsimp only [BufferTree.root]
  apply StmtDepthBound.mono
  · ram_source_depth_step
  · simp

set_option maxHeartbeats 400000 in
/-- Every successful realization of the declared body can use at most one
nested frame per two tree levels. Representation is used only to identify
the actual read values and recursive grandchild, not to re-prove correctness.
Sequential helper calls combine by maximum, rather than accumulating frames. -/
theorem splay_depthBound_at (key : Nat → Nat) (query : Nat) (tree : Tree Nat) :
    FunctionDepthBound Implementation.program Implementation.splayId
      (splayCostPre key query tree) (fun _ _ => splayDepthBound tree) := by
  have allTrees : ∀ n (tree : Tree Nat), tree.numNodes = n →
      FunctionDepthBound Implementation.program Implementation.splayId
        (splayCostPre key query tree) (fun _ _ => splayDepthBound tree) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro tree size
      cases tree with
      | nil => exact splay_nil_depthBound key query
      | node root a b =>
        ram_source_depth_intro (keys left right currentRoot currentQuery)
        intro heap input
        simp only [splayCostPre, Implementation.splay_onArgs, Env.head_cons, Env.tail_cons] at input
        rcases input with ⟨rootEq, queryEq, represented⟩
        subst currentRoot currentQuery
        rcases BufferTree.Rep.node_iff.mp represented with
          ⟨nonzero, readKey, readLeft, readRight, repA, repB⟩
        dsimp only [BufferTree.root]
        apply Classical.byCases (p := query < key root)
        · intro toLeft
          cases a with
          | nil =>
            simp only [BufferTree.root] at readLeft
            apply StmtDepthBound.mono
            · ram_source_depth_step
            · simp only [splayDepthBound, Tree.height]
              omega
          | node child x y =>
            rcases BufferTree.Rep.node_iff.mp repA with
              ⟨childNonzero, readChildKey, readChildLeft, readChildRight, repX, repY⟩
            simp only [BufferTree.root] at readLeft
            apply Classical.byCases (p := query < key child)
            · intro toLeftLeft
              have smaller : x.numNodes < n := by simp only [Tree.numNodes] at size; omega
              have recursive := ih x.numNodes smaller x rfl
              have descent : splayDepthBound x + 1 ≤
                  splayDepthBound (.node root (.node child x y) b) := by
                simp only [splayDepthBound, Tree.height]
                omega
              apply StmtDepthBound.mono
              · ram_source_depth_step using [recursive, rotateRight_depthBound]
                all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                  Env.head_cons, Env.tail_cons,
                  Except.ok.injEq, and_self]
              · omega
            · intro toLeftLeft
              apply Classical.byCases (p := key child < query)
              · intro toLeftRight
                have smaller : y.numNodes < n := by simp only [Tree.numNodes] at size; omega
                have recursive := ih y.numNodes smaller y rfl
                have descent : splayDepthBound y + 1 ≤
                    splayDepthBound (.node root (.node child x y) b) := by
                  simp only [splayDepthBound, Tree.height]
                  omega
                apply StmtDepthBound.mono
                · ram_source_depth_step using [recursive, rotateRight_depthBound,
                    rotateLeft_depthBound]
                  all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                    Env.head_cons, Env.tail_cons,
                    Except.ok.injEq, and_self]
                · omega
              · intro toLeftRight
                apply StmtDepthBound.mono
                · ram_source_depth_step using rotateRight_depthBound
                  all_goals trivial
                · simp only [splayDepthBound, Tree.height]
                  omega
        · intro toLeft
          apply Classical.byCases (p := key root < query)
          · intro toRight
            cases b with
            | nil =>
              simp only [BufferTree.root] at readRight
              apply StmtDepthBound.mono
              · ram_source_depth_step
              · simp only [splayDepthBound, Tree.height]
                omega
            | node child x y =>
              rcases BufferTree.Rep.node_iff.mp repB with
                ⟨childNonzero, readChildKey, readChildLeft, readChildRight, repX, repY⟩
              simp only [BufferTree.root] at readRight
              apply Classical.byCases (p := key child < query)
              · intro toRightRight
                have smaller : y.numNodes < n := by simp only [Tree.numNodes] at size; omega
                have recursive := ih y.numNodes smaller y rfl
                have descent : splayDepthBound y + 1 ≤
                    splayDepthBound (.node root a (.node child x y)) := by
                  simp only [splayDepthBound, Tree.height]
                  omega
                apply StmtDepthBound.mono
                · ram_source_depth_step using [recursive, rotateLeft_depthBound]
                  all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                    Env.head_cons, Env.tail_cons,
                    Except.ok.injEq, and_self]
                · omega
              · intro toRightRight
                apply Classical.byCases (p := query < key child)
                · intro toRightLeft
                  have smaller : x.numNodes < n := by simp only [Tree.numNodes] at size; omega
                  have recursive := ih x.numNodes smaller x rfl
                  have descent : splayDepthBound x + 1 ≤
                      splayDepthBound (.node root a (.node child x y)) := by
                    simp only [splayDepthBound, Tree.height]
                    omega
                  apply StmtDepthBound.mono
                  · ram_source_depth_step using [recursive, rotateRight_depthBound,
                      rotateLeft_depthBound]
                    all_goals simp_all only [splayCostPre, Implementation.splay_onArgs,
                      Env.head_cons, Env.tail_cons,
                      Except.ok.injEq, and_self]
                  · omega
                · intro toRightLeft
                  apply StmtDepthBound.mono
                  · ram_source_depth_step using rotateLeft_depthBound
                    all_goals trivial
                  · simp only [splayDepthBound, Tree.height]
                    omega
          · intro toRight
            apply StmtDepthBound.mono
            · ram_source_depth_step
            · simp only [splayDepthBound, Tree.height]
              omega
  exact allTrees tree.numNodes tree rfl

/-- The node count gives a shape-independent nesting bound for consecutive
accesses, even when rotations change the height between invocations. -/
theorem splayDepthBound_le_numNodes (tree : Tree Nat) :
    splayDepthBound tree ≤ tree.numNodes / 2 := by
  have heightBound := Tree.height_le_numNodes tree
  unfold splayDepthBound
  omega

end Complexity.Language.Examples.Splay
