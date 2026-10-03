/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Prepare
import Complexity.Computability.Ram.Execution.Space

/-!
# Physical space of the existing current-list preparation

Each constructor retains the preceding physical footprint and adds every
address accessed by its actual compiled invocation, including node initialization
and call frames. No new loader, runner, or author-selected access relation is
introduced. External input transport and the grader's own storage are excluded.
-/

namespace Ram.LanguageCompiler.List.Prepare

open Complexity.Language

variable (kind : CellTy) {w heapLimit : Nat}

/-- The same real constructor calls, with their cumulative physical addresses. -/
inductive SpaceRun : _root_.List (CellValue kind) → Option (NodeRef kind) →
    Session.State w heapLimit → Option (NodeRef kind) →
    Session.State w heapLimit → Nat → Finset (Word w) → Finset (Word w) → Prop
  | nil (tail current seed) : SpaceRun [] tail current tail current 0 seed seed
  | cons {head values tail current root middle steps seed footprint}
      (rest : SpaceRun values tail current root middle steps seed footprint)
      (outcome : FunctionArenaExecution (List.Cons.program kind) (List.Cons.entry kind)
        0 heapLimit middle.placement (List.Cons.args kind head root)
        middle.heap middle.entry) :
      SpaceRun (head :: values) tail current outcome.value (Session.State.ofExecution outcome)
        (steps + outcome.result.steps) seed (footprint ∪ outcome.heapAccesses)

variable {kind}

/-- Erasure retains exactly the original counted preparation and final memory. -/
theorem SpaceRun.erase {values : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun kind values tail current root finish steps seed footprint) :
    Run kind values tail current root finish steps := by
  induction run with
  | nil => exact .nil _ _
  | cons rest outcome ih => exact .cons ih outcome

/-- The initial resident words are never dropped between constructor calls. -/
theorem SpaceRun.seed_subset {values : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun kind values tail current root finish steps seed footprint) :
    seed ⊆ footprint := by
  induction run with
  | nil => exact fun _ member => member
  | cons rest outcome ih => exact ih.trans Finset.subset_union_left

/-- Observe the given real preparation, without choosing different executions. -/
theorem Run.withSpace {values : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} (run : Run kind values tail current root finish steps)
    (seed : Finset (Word w)) :
    ∃ footprint, SpaceRun kind values tail current root finish steps seed footprint := by
  induction run with
  | nil => exact ⟨seed, .nil _ _ _⟩
  | cons rest outcome ih =>
      obtain ⟨footprint, observed⟩ := ih
      exact ⟨footprint ∪ outcome.heapAccesses, .cons observed outcome⟩

/-- A conservative bound from the actual invocations: a RAM transition accesses
at most one physical word. Repeated addresses are counted only once. -/
theorem SpaceRun.card_le {values : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} {seed footprint : Finset (Word w)}
    (run : SpaceRun kind values tail current root finish steps seed footprint) :
    footprint.card ≤ seed.card + steps := by
  induction run with
  | nil => simp
  | cons rest outcome ih =>
      have accessed : outcome.heapAccesses.card ≤ outcome.result.steps := by
        exact Ram.heapAccesses_card_le _ _ _
      exact (Finset.card_union_le _ _).trans
        ((Nat.add_le_add ih accessed).trans_eq (Nat.add_assoc _ _ _))

/-- Fixed single-list request adapter for prepared sessions. The retained suffix
is an explicit fixed root, not future input or reconstructed private state. -/
def prepare (kind : CellTy) (tail : Option (NodeRef kind))
    (values : _root_.List (CellValue kind)) (current : Session.State w heapLimit)
    (args : Env [.option (.node kind)]) (finish : Session.State w heapLimit) (steps : Nat) : Prop :=
  Run kind values tail current args.head finish steps

/-- The adapter's addresses are determined by the same constructor invocations. -/
def prepareSpace (kind : CellTy) (tail : Option (NodeRef kind))
    (values : _root_.List (CellValue kind)) (current : Session.State w heapLimit)
    (args : Env [.option (.node kind)]) (finish : Session.State w heapLimit) (steps : Nat)
    (seed footprint : Finset (Word w)) : Prop :=
  SpaceRun kind values tail current args.head finish steps seed footprint

/-- Direct compatibility with the fixed counted preparation of a session. -/
theorem prepareSpace_erase {tail : Option (NodeRef kind)}
    {values : _root_.List (CellValue kind)} {current finish : Session.State w heapLimit}
    {args : Env [.option (.node kind)]} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace kind tail values current args finish steps seed footprint) :
    prepare kind tail values current args finish steps := run.erase

/-- The session adapter uses the existing source loader, not an arbitrary
mathematical reconstruction of the prepared list or retained heap. -/
theorem prepareSpace_source {tail : Option (NodeRef kind)}
    {values : _root_.List (CellValue kind)} {current finish : Session.State w heapLimit}
    {args : Env [.option (.node kind)]} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace kind tail values current args finish steps seed footprint) :
    Complexity.Language.List.Prepare.Run kind values tail current.heap args.head
      finish.heap := run.erase.source

theorem prepareSpace_seed_subset {tail : Option (NodeRef kind)}
    {values : _root_.List (CellValue kind)} {current finish : Session.State w heapLimit}
    {args : Env [.option (.node kind)]} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : prepareSpace kind tail values current args finish steps seed footprint) :
    seed ⊆ footprint := run.seed_subset

/-- The existing loader's realization and instruction theorem supply a finite
space bound for the very same prepared input and retained source suffix. -/
theorem exists_space_le (kind : CellTy) (values suffix : _root_.List (CellValue kind))
    (tail : Option (NodeRef kind)) (current : Session.State w heapLimit)
    (capacity : FunctionCapacity (List.Cons.program kind) (List.Cons.entry kind)
      w 0 heapLimit)
    (fits : ∀ value ∈ values, ValueFits w (kind.toValue value))
    (space : current.cursor + 3 * values.length ≤ heapLimit)
    (observed : (Representation.list kind).Rel suffix tail current.heap)
    (seed : Finset (Word w)) :
    ∃ root finish steps footprint,
      SpaceRun kind values tail current root finish steps seed footprint ∧
      (Representation.list kind).Rel (values ++ suffix) root finish.heap ∧
      finish.cursor = current.cursor + 3 * values.length ∧
      footprint.card ≤ seed.card + values.length * List.Cons.steps kind := by
  obtain ⟨root, finish, steps, run, represented, cursor, counted⟩ :=
    exists_le kind values suffix tail current capacity fits space observed
  obtain ⟨footprint, actual⟩ := run.withSpace seed
  exact ⟨root, finish, steps, footprint, actual, represented, cursor,
    actual.card_le.trans (Nat.add_le_add_left counted seed.card)⟩

end Ram.LanguageCompiler.List.Prepare
