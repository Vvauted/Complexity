/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.PreparedWorstCaseTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared

/-!
# Physical-word bounds for PreparedWorstCase session executions

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
def PreparedWorstCaseSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x environment, valid x environment →
      ∀ inputs replies finish finalHeap,
        session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
        accept x environment inputs replies →
        ∀ w, ∀ admitted : widthWith overhead x (admissionWords x environment) ≤ w,
          ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
              (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
            Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
              (Complexity.Program.Input.args x)
              (Ram.LanguageCompiler.Session.State.ofInput x w (widthWith_base admitted))
              inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
            finalWorld.heap = finalHeap ∧ footprint.card ≤ bound (size x environment)


/-- Actual instruction counts and physical words on one shared execution.
Independent time and space witnesses must not be substituted for this claim. -/
def PreparedWorstCaseTimeSpaceO
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
      (fun n => (timeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
      (fun n => (spaceGrowth n : ℝ)) ∧
    ∀ x environment, valid x environment →
      ∀ inputs replies finish finalHeap,
        session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
          (Complexity.Program.Input.heap x) inputs replies finish finalHeap →
        accept x environment inputs replies →
        ∀ w, ∀ admitted : widthWith overhead x (admissionWords x environment) ≤ w,
          ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
              (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
            Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
              (Complexity.Program.Input.args x)
              (Ram.LanguageCompiler.Session.State.ofInput x w (widthWith_base admitted))
              inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
            finalWorld.heap = finalHeap ∧ steps ≤ timeBound (size x environment) ∧ footprint.card ≤ spaceBound (size x environment)


/-- Project the space bound without changing the accepted execution. -/
theorem PreparedWorstCaseTimeSpaceO.space
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.PreparedWorstCaseTimeSpaceO sourcePrepare prepareSpace admissionWords valid accept size timeGrowth spaceGrowth) :
    session.PreparedWorstCaseSpaceO sourcePrepare prepareSpace admissionWords valid accept size spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, spaceBound, spaceAsymptotic, ?_⟩
  intro x environment legal inputs replies finish finalHeap source accepted w admitted
  obtain ⟨finalWorld, steps, footprint, run, sameHeap, timeCost, spaceCost⟩ := runs x environment legal inputs replies finish finalHeap source accepted w admitted
  exact ⟨finalWorld, steps, footprint, run, sameHeap, spaceCost⟩

/-- Project the actual time bound of this same physical-footprint trace. -/
theorem PreparedWorstCaseTimeSpaceO.time
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepare : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (preparation_erase : ∀ {w heapLimit : Nat} input
      (current : Ram.LanguageCompiler.Session.State w heapLimit) args prepared steps seed footprint,
      prepareSpace input current args prepared steps seed footprint →
        prepare input current args prepared steps)
    (bounded : session.PreparedWorstCaseTimeSpaceO sourcePrepare prepareSpace admissionWords valid accept size timeGrowth spaceGrowth) :
    session.PreparedWorstCaseTimeO sourcePrepare prepare admissionWords valid accept size timeGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, timeBound, timeAsymptotic, ?_⟩
  intro x environment legal inputs replies finish finalHeap source accepted w admitted
  obtain ⟨finalWorld, steps, footprint, run, sameHeap, timeCost, spaceCost⟩ := runs x environment legal inputs replies finish finalHeap source accepted w admitted
  exact ⟨finalWorld, steps, run.erase preparation_erase, sameHeap, timeCost⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev PreparedWorstCaseSpaceOOn
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (growth : (x : α) → ω x → Nat) : Prop :=
  session.PreparedWorstCaseSpaceO sourcePrepare prepareSpace admissionWords valid accept growth id

/-- Restrict legality without changing admission, footprint or source entries. -/
theorem PreparedWorstCaseSpaceO.mono_valid
    (session : Session (Complexity.Program.Input.params α) request response)
    (sourcePrepare : ι → Heap → Env request → Heap → Prop)
    (prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop)
    (admissionWords : (x : α) → ω x → Array Nat)
    (valid valid' : (x : α) → ω x → Prop)
    (accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop)
    (size : (x : α) → ω x → Nat) (growth : Nat → Nat)
    (space : session.PreparedWorstCaseSpaceO sourcePrepare prepareSpace admissionWords valid accept size growth)
    (restrict : ∀ x environment, valid' x environment → valid x environment) :
    session.PreparedWorstCaseSpaceO sourcePrepare prepareSpace admissionWords valid' accept size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x environment legal
  exact runs x environment (restrict x environment legal)

/-- Realize the given successful source trace with its actual physical footprint. -/
theorem PreparedWorstCaseSpaceO.realizes
    {session : Session (Complexity.Program.Input.params α) request response}
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    {prepareSpace : ∀ {w heapLimit : Nat}, ι →
      Ram.LanguageCompiler.Session.State w heapLimit → Env request →
      Ram.LanguageCompiler.Session.State w heapLimit → Nat →
      Finset (Ram.Word w) → Finset (Ram.Word w) → Prop}
    {admissionWords : (x : α) → ω x → Array Nat}
    {valid : (x : α) → ω x → Prop}
    {accept : (x : α) → ω x → List ι → List (Value response × Heap) → Prop}
    {size : (x : α) → ω x → Nat} {growth : Nat → Nat}
    (space : session.PreparedWorstCaseSpaceO sourcePrepare prepareSpace admissionWords
      valid accept size growth)
    {x : α} {environment : ω x} (legal : valid x environment)
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {finalHeap : Heap}
    (source : session.PreparedRuns sourcePrepare (Complexity.Program.Input.args x)
      (Complexity.Program.Input.heap x) inputs replies finish finalHeap)
    (accepted : accept x environment inputs replies) :
    ∃ w, ∃ base : 1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
        (Complexity.Program.RamInput.words x) ≤ w,
      ∃ (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.PreparedSpaceRuns session prepareSpace
          (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w base)
          inputs replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧ finalWorld.heap = finalHeap := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨finalWorld, steps, footprint, run, sameHeap, counted⟩ :=
    runs x environment legal inputs replies finish finalHeap source accepted
      (widthWith overhead x (admissionWords x environment)) (Nat.le_refl _)
  exact ⟨_, widthWith_base (Nat.le_refl _), finalWorld, steps, footprint, run, sameHeap⟩

end Complexity.Language.Session
