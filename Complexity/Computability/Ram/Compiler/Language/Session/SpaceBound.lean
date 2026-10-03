/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.Space

/-!
# Physical-word bounds for  session executions

These bounds use the same domain, width admission and information boundary as
the corresponding time interface. A fixed initial seed is the preloaded arena
prefix, including metadata, not a purported exact set of reachable live cells.
Every actual invocation unions its heap accesses into that seed; reused addresses
count once. Registers, code, oracle work and external driver/transport are out.
The time-and-space interface bounds one and the same decorated execution, not
two separately selected successful histories. No change to source execution or
runtime is made. Correctness and termination remain independent obligations.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}


/-- Uniform cumulative physical words on the same actual initialized trace. -/
def SpaceO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w, ∀ admitted : Complexity.Program.width overhead x ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        footprint.card ≤ bound (size x inputs)


/-- Actual instruction counts and physical words on one shared execution.
Independent time and space witnesses must not be substituted for this claim. -/
def TimeSpaceO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ timeBound spaceBound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (timeBound n : ℝ))
      (fun n => (timeGrowth n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (spaceBound n : ℝ))
      (fun n => (spaceGrowth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w, ∀ admitted : Complexity.Program.width overhead x ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat) (footprint : Finset (Ram.Word w)),
        Ram.LanguageCompiler.Session.SpaceRuns session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          (inputs.map encode) replies finish finalWorld steps
          (Ram.initialSegment w (Complexity.Program.RamInput.cursor x)) footprint ∧
        steps ≤ timeBound (size x inputs) ∧ footprint.card ≤ spaceBound (size x inputs)


/-- Project the space bound without changing the accepted execution. -/
theorem TimeSpaceO.space (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.TimeSpaceO encode valid size timeGrowth spaceGrowth) :
    session.SpaceO encode valid size spaceGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, spaceBound, spaceAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run, timeCost, spaceCost⟩ := runs x inputs legal w admitted
  exact ⟨fits, replies, finish, finalWorld, steps, footprint, run, spaceCost⟩

/-- Project the actual time bound of this same physical-footprint trace. -/
theorem TimeSpaceO.time (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (size : α → List ι → Nat) (timeGrowth spaceGrowth : Nat → Nat)
    (bounded : session.TimeSpaceO encode valid size timeGrowth spaceGrowth) :
    session.TimeO encode valid size timeGrowth := by
  obtain ⟨overhead, timeBound, spaceBound, timeAsymptotic, spaceAsymptotic, runs⟩ := bounded
  refine ⟨overhead, timeBound, timeAsymptotic, ?_⟩
  intro x inputs legal w admitted
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run, timeCost, spaceCost⟩ := runs x inputs legal w admitted
  exact ⟨fits, replies, finish, finalWorld, steps, run.erase, timeCost⟩

/-- State the mathematical physical-space scale directly on the protocol data. -/
abbrev SpaceOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (growth : α → List ι → Nat) : Prop :=
  session.SpaceO encode valid growth id

/-- Restrict legality without changing admission, footprint or source entries. -/
theorem SpaceO.mono_valid (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid valid' : α → List ι → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat)
    (space : session.SpaceO encode valid size growth)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.SpaceO encode valid' size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  refine ⟨overhead, bound, asymptotic, ?_⟩
  intro x inputs legal
  exact runs x inputs (restrict x inputs legal)

/-- The given uniform word-space requirement supplies the same initialized
source execution, without requiring a proposed source time budget. -/
theorem SpaceO.source
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid : α → List ι → Prop}
    {size : α → List ι → Nat} {growth : Nat → Nat}
    (space : session.SpaceO encode valid size growth)
    {x : α} {inputs : List ι} (legal : valid x inputs) :
    ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
      (finalHeap : Heap),
      session.Runs (Complexity.Program.Input.args x) (Complexity.Program.Input.heap x)
        (inputs.map encode) replies finish finalHeap := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := space
  obtain ⟨fits, replies, finish, finalWorld, steps, footprint, run, words⟩ :=
    runs x inputs legal (Complexity.Program.width overhead x) (Nat.le_refl _)
  exact ⟨replies, finish, finalWorld.heap, run.source⟩

end Complexity.Language.Session
