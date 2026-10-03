/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.PreparedHistoryTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared

/-!
# Physical-word bounds for PreparedHistory session executions

These bounds use the same domain, width admission and information boundary as
the corresponding time interface. A fixed initial seed is the preloaded arena
prefix, including metadata, not a purported exact set of reachable live cells.
Every actual invocation unions its heap accesses into that seed; reused addresses
count once. Registers, code, oracle work and external driver/transport are out.
The time-and-space interface bounds one and the same decorated execution, not
two separately selected successful histories. No change to source execution or
runtime is made. Correctness and termination remain independent obligations.
The author fixes a concrete execution-backed preparation-space relation;
a relation or annotation without the concrete loader's evidence is insufficient.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}


/-- Uniform cumulative physical words on the same actual initialized trace. -/
def PreparedHistorySpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyWidth overhead requestWords x inputs ≤ w,
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        post x inputs replies ∧ footprint.card ≤ bound (size x inputs)


/-- Actual instruction counts and physical words on one shared execution.
Independent time and space witnesses must not be substituted for this claim. -/
def PreparedHistoryTimeSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
      (fun n => (timeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
      (fun n => (spaceGrowth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w,
      ∀ admitted : historyWidth overhead requestWords x inputs ≤ w,
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        post x inputs replies ∧ steps ≤ timeBound (size x inputs) ∧ footprint.card ≤ spaceBound (size x inputs)


/-- Project the space bound without changing the accepted execution. -/
theorem PreparedHistoryTimeSpaceO.space
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.PreparedHistoryTimeSpaceO prepareSpace requestWords valid post size timeGrowth spaceGrowth) :
    session.PreparedHistorySpaceO prepareSpace requestWords valid post size spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, spaceBound, spaceAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨replies, finish, finalWorld, steps, footprint, run, observed, timeCost, spaceCost⟩ := runs x inputs legal w admitted
  exact ⟨replies, finish, finalWorld, steps, footprint, run, observed, spaceCost⟩

/-- Project the actual time bound of this same physical-footprint trace. -/
theorem PreparedHistoryTimeSpaceO.time
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (preparation_erase : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        prepare input current args prepared steps)
    (bounded : session.PreparedHistoryTimeSpaceO prepareSpace requestWords valid post size timeGrowth spaceGrowth) :
    session.PreparedHistoryTimeO prepare requestWords valid post size timeGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, timeBound, timeAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨replies, finish, finalWorld, steps, footprint, run, observed, timeCost, spaceCost⟩ := runs x inputs legal w admitted
  exact ⟨replies, finish, finalWorld, steps, run.erase preparation_erase, observed, timeCost⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev PreparedHistorySpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (growth : α → List ι → Nat) : Prop :=
  session.PreparedHistorySpaceO prepareSpace requestWords valid post growth id

/-- Restrict legality without changing admission, footprint or source entries. -/
theorem PreparedHistorySpaceO.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (requestWords : ι → Array Nat)
    (valid valid' : α → List ι → Prop)
    (post : α → List ι → List (Value response × Heap) → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat)
    (space : session.PreparedHistorySpaceO prepareSpace requestWords valid post size growth)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.PreparedHistorySpaceO prepareSpace requestWords valid' post size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x inputs legal
  exact runs x inputs (restrict x inputs legal)

/-- Project the same physical-word trace to independent source behavior. -/
theorem PreparedHistorySpaceO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {requestWords : ι → Array Nat} {valid : α → List ι → Prop}
    {post : α → List ι → List (Value response × Heap) → Prop}
    {size : α → List ι → Nat} {growth : Nat → Nat}
    (preparation_source : ∀ {w heapLimit} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    (space : session.PreparedHistorySpaceO prepareSpace requestWords valid post size growth)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalHeap : Heap),
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
      post x inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨replies, finish, finalWorld, steps, footprint, run, observed, cost⟩ :=
    runs x inputs legal (historyWidth overhead requestWords x inputs) (Nat.le_refl _)
  exact ⟨replies, finish, finalWorld.heap, run.source preparation_source, observed⟩

end Complexity.Language.Session
