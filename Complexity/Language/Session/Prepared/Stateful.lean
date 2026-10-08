/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session.Prepared

/-!
# Prepared sessions with retained loader state

A fixed current-request loader may retain a buffer descriptor between calls.
Its state is indexed explicitly at both ends of the history: a descriptor
returned by one preparation is the descriptor supplied to the next, at the
actual heap returned by the intervening callback. Initialization uses the
interface's fixed initial loader state, not a state selected for each request.

This decorates the existing source calls. It neither implements a loader nor
assigns costs to an arbitrary preparation relation. On a reused buffer, the
concrete loader supplies its real overwrite and frame properties.
-/

namespace Complexity.Language.Session

universe u v
variable {ι : Type u} {δ : Type v}
variable {configuration request : List Ty} {response : Ty}
variable (session : Session configuration request response)
variable (prepare : δ → ι → Heap → Env request → Heap → δ → Prop)

/-- Interleave preparation and actual calls while threading the loader's exact
state across the actual returned heaps. Reply observations retain those heaps. -/
inductive StatefulPreparedRun : δ → Value session.stateTy → Heap → List ι →
    List (Value response × Heap) → δ → Value session.stateTy → Heap → Prop
  | nil (cache state heap) : StatefulPreparedRun cache state heap [] [] cache state heap
  | cons {cache state heap input args prepared nextCache reply next intermediate
      inputs replies finalCache finish finalHeap}
      (loaded : prepare cache input heap args prepared nextCache)
      (called : session.Step state prepared args reply next intermediate)
      (rest : StatefulPreparedRun nextCache next intermediate inputs replies
        finalCache finish finalHeap) :
      StatefulPreparedRun cache state heap (input :: inputs) ((reply, intermediate) :: replies)
        finalCache finish finalHeap

/-- Initialize the actual session once, using the interface-fixed loader state.
A reusable-buffer loader normally supplies `none` as `initialCache`. -/
def StatefulPreparedRuns (initialCache : δ) (args : Env configuration) (heap : Heap)
    (inputs : List ι) (replies : List (Value response × Heap)) (finalCache : δ)
    (finish : Value session.stateTy) (finalHeap : Heap) : Prop :=
  ∃ state initialized, session.Starts args heap state initialized ∧
    session.StatefulPreparedRun prepare initialCache state initialized inputs replies
      finalCache finish finalHeap

variable {session prepare}

/-- Each prepared request has exactly one actual callback reply. -/
theorem StatefulPreparedRun.length
    {cache finalCache : δ} {state finish : Value session.stateTy} {heap finalHeap : Heap}
    {inputs : List ι} {replies : List (Value response × Heap)}
    (run : session.StatefulPreparedRun prepare cache state heap inputs replies
      finalCache finish finalHeap) : replies.length = inputs.length := by
  induction run with
  | nil => rfl
  | cons loaded called rest ih => exact congrArg Nat.succ ih

/-- Compose at the actual intermediate callback state, loader state and heap. -/
theorem StatefulPreparedRun.append
    {cache middleCache finalCache : δ} {state middle finish : Value session.stateTy}
    {heap intermediate finalHeap : Heap} {inputs₁ inputs₂ : List ι}
    {replies₁ replies₂ : List (Value response × Heap)}
    (first : session.StatefulPreparedRun prepare cache state heap inputs₁ replies₁
      middleCache middle intermediate)
    (second : session.StatefulPreparedRun prepare middleCache middle intermediate inputs₂
      replies₂ finalCache finish finalHeap) :
    session.StatefulPreparedRun prepare cache state heap (inputs₁ ++ inputs₂)
      (replies₁ ++ replies₂) finalCache finish finalHeap := by
  induction first with
  | nil => exact second
  | cons loaded called rest ih => exact .cons loaded called (ih second)

/-- Forget loader-state observations only after obtaining the same complete
state-threaded execution. This implication does not reconstruct a retained cache. -/
theorem StatefulPreparedRun.erase
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    (preparation_erase : ∀ cache input heap args prepared nextCache,
      prepare cache input heap args prepared nextCache → sourcePrepare input heap args prepared)
    {cache finalCache : δ} {state finish : Value session.stateTy} {heap finalHeap : Heap}
    {inputs : List ι} {replies : List (Value response × Heap)}
    (run : session.StatefulPreparedRun prepare cache state heap inputs replies
      finalCache finish finalHeap) :
    session.PreparedRun sourcePrepare state heap inputs replies finish finalHeap := by
  induction run with
  | nil => exact .nil _ _
  | cons loaded called rest ih =>
      exact .cons (preparation_erase _ _ _ _ _ _ loaded) called ih

/-- Forget loader-state observations while retaining initialization and all
actual return heaps of the same source history. -/
theorem StatefulPreparedRuns.erase
    {sourcePrepare : ι → Heap → Env request → Heap → Prop}
    (preparation_erase : ∀ cache input heap args prepared nextCache,
      prepare cache input heap args prepared nextCache → sourcePrepare input heap args prepared)
    {initialCache finalCache : δ} {args : Env configuration} {heap finalHeap : Heap}
    {inputs : List ι} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy}
    (run : session.StatefulPreparedRuns prepare initialCache args heap inputs replies
      finalCache finish finalHeap) :
    session.PreparedRuns sourcePrepare args heap inputs replies finish finalHeap := by
  obtain ⟨state, initialized, started, rest⟩ := run
  exact ⟨state, initialized, started, rest.erase preparation_erase⟩

end Complexity.Language.Session
