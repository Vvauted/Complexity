/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.PreparedTraceTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared

/-!
# Physical-word bounds for PreparedTrace session executions

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
variable {ι : Type u} {ω : α → Type v} {request : List Ty} {response : Ty}


/-- Uniform cumulative physical words on the same actual initialized trace. -/
def PreparedTraceSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.width overhead x ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧ footprint.card ≤ bound (size x environment)


/-- Actual instruction counts and physical words on one shared execution.
Independent time and space witnesses must not be substituted for this claim. -/
def PreparedTraceTimeSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
      (fun n => (timeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
      (fun n => (spaceGrowth n : ℝ)) ∧
    ∀ x environment, valid x environment → ∀ w,
      ∀ admitted : Complexity.Program.width overhead x ≤ w,
      ∃ (inputs : List ι) (replies : List (Value response × Heap))
        (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        accept x environment inputs replies ∧ steps ≤ timeBound (size x environment) ∧ footprint.card ≤ spaceBound (size x environment)


/-- Project the space bound without changing the accepted execution. -/
theorem PreparedTraceTimeSpaceO.space
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.PreparedTraceTimeSpaceO prepareSpace valid accept size timeGrowth spaceGrowth) :
    session.PreparedTraceSpaceO prepareSpace valid accept size spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, spaceBound, spaceAsymptotic, ?_⟩
  intro x environment legal w admitted
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, run, accepted, timeCost, spaceCost⟩ := runs x environment legal w admitted
  exact ⟨inputs, replies, finish, finalWorld, steps, footprint, run, accepted, spaceCost⟩

/-- Project the actual time bound of this same physical-footprint trace. -/
theorem PreparedTraceTimeSpaceO.time
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (preparation_erase : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        prepare input current args prepared steps)
    (bounded : session.PreparedTraceTimeSpaceO prepareSpace valid accept size timeGrowth spaceGrowth) :
    session.PreparedTraceTimeO prepare valid accept size timeGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, timeBound, timeAsymptotic, ?_⟩
  intro x environment legal w admitted
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, run, accepted, timeCost, spaceCost⟩ := runs x environment legal w admitted
  exact ⟨inputs, replies, finish, finalWorld, steps, run.erase preparation_erase, accepted, timeCost⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev PreparedTraceSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → ω x → Nat) : Prop :=
  session.PreparedTraceSpaceO prepareSpace valid accept growth id

/-- Restrict legality without changing admission, footprint or source entries. -/
theorem PreparedTraceSpaceO.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (valid valid' : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat)
    (space : session.PreparedTraceSpaceO prepareSpace valid accept size growth)
    (restrict : ∀ x environment, valid' x environment → valid x environment) :
    session.PreparedTraceSpaceO prepareSpace valid' accept size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x environment legal
  exact runs x environment (restrict x environment legal)

/-- Project the same physical-word trace to independent source behavior. -/
theorem PreparedTraceSpaceO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → ω x → Nat} {growth : Nat → Nat}
    (preparation_source : ∀ {w heapLimit} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        sourcePrepare input current.heap args prepared.heap)
    (space : session.PreparedTraceSpaceO prepareSpace valid accept size growth)
    {x : α} {environment : ω x} (legal : valid x environment) :
    ∃ (inputs : List ι) (replies : List (Value response × Heap))
      (finish : Value session.stateTy) (finalHeap : Heap),
      session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
        (Complexity.Program.Input.heap x) inputs replies finish finalHeap ∧
        accept x environment inputs replies := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨inputs, replies, finish, finalWorld, steps, footprint, run, accepted, cost⟩ :=
    runs x environment legal (Complexity.Program.width overhead x) (Nat.le_refl _)
  exact ⟨inputs, replies, finish, finalWorld.heap,
    run.source preparation_source, accepted⟩

end Complexity.Language.Session
