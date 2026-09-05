import Ram.Execution

/-!
# A budget runner that preserves results

`run` executes at most its budget, stops immediately after halt or an input
fault, and always returns the final state and the number of real transitions.
An exhausted budget is not a proof of divergence. With zero budget a running
state reports `outOfFuel`; an invalid PC is discovered when a step is attempted.

The tail-recursive driver is shared with efficient state representations. Its
implementation bookkeeping does not introduce a second machine cost model.
-/

namespace Ram

inductive StopReason where
  | halted
  | fault
  | invalidPC
  | outOfFuel
  deriving DecidableEq, Repr

structure RunResult (σ : Type) where
  state : σ
  steps : Nat
  reason : StopReason

/-- Change only the state representation, retaining time and stopping reason. -/
def RunResult.map (f : σ → τ) (r : RunResult σ) : RunResult τ :=
  ⟨f r.state, r.steps, r.reason⟩

namespace Runner

/-- Tail-recursive driver. `count` records transitions already performed. -/
def loop (next : σ → Option σ) (status : σ → Status) :
    Nat → Nat → σ → RunResult σ
  | fuel, count, s =>
    match status s with
    | .halted => ⟨s, count, .halted⟩
    | .fault => ⟨s, count, .fault⟩
    | .running =>
      match fuel with
      | 0 => ⟨s, count, .outOfFuel⟩
      | fuel + 1 =>
        match next s with
        | none => ⟨s, count, .invalidPC⟩
        | some t => loop next status fuel (count + 1) t

/-- A backend-independent runner with observable stopping reasons. -/
def runWith (next : σ → Option σ) (status : σ → Status)
    (budget : Nat) (s : σ) : RunResult σ := loop next status budget 0 s

/-- An exact backend simulation preserves the entire observable run result. -/
theorem loop_map {nextA : σ → Option σ} {nextB : τ → Option τ}
    {statusA : σ → Status} {statusB : τ → Status} (f : σ → τ)
    (next_map : ∀ s, (nextA s).map f = nextB (f s))
    (status_map : ∀ s, statusA s = statusB (f s))
    (fuel count : Nat) (s : σ) :
    (loop nextA statusA fuel count s).map f =
      loop nextB statusB fuel count (f s) := by
  induction fuel generalizing count s with
  | zero =>
    cases hs : statusA s <;> simp [loop, ← status_map s, hs, RunResult.map]
  | succ fuel ih =>
    cases hs : statusA s with
    | halted => simp [loop, ← status_map s, hs, RunResult.map]
    | fault => simp [loop, ← status_map s, hs, RunResult.map]
    | running =>
      cases hn : nextA s with
      | none => simp [loop, ← status_map s, hs, ← next_map s, hn, RunResult.map]
      | some t =>
        simpa [loop, ← status_map s, hs, ← next_map s, hn] using ih (count + 1) t

theorem runWith_map {nextA : σ → Option σ} {nextB : τ → Option τ}
    {statusA : σ → Status} {statusB : τ → Status} (f : σ → τ)
    (next_map : ∀ s, (nextA s).map f = nextB (f s))
    (status_map : ∀ s, statusA s = statusB (f s))
    (budget : Nat) (s : σ) :
    (runWith nextA statusA budget s).map f = runWith nextB statusB budget (f s) :=
  loop_map f next_map status_map budget 0 s

/-- Any backend whose transitions simulate `step` retains an exact execution
trace and cannot spend more transitions than its budget. -/
theorem loop_exec {code : Code} {next : σ → Option σ} {status : σ → Status}
    (decode : σ → State w)
    (next_sound : ∀ s t, next s = some t → step code (decode s) = some (decode t))
    (fuel count : Nat) (s : σ) :
    ∃ k, (loop next status fuel count s).steps = count + k ∧ k ≤ fuel ∧
      Exec code k (decode s) (decode (loop next status fuel count s).state) := by
  induction fuel generalizing count s with
  | zero =>
    cases hs : status s <;>
      exact ⟨0, by simp [loop, hs], Nat.le_refl 0, by simp [loop, hs]⟩
  | succ fuel ih =>
    cases hs : status s with
    | halted => exact ⟨0, by simp [loop, hs], Nat.zero_le _, by simp [loop, hs]⟩
    | fault => exact ⟨0, by simp [loop, hs], Nat.zero_le _, by simp [loop, hs]⟩
    | running =>
      cases hn : next s with
      | none => exact ⟨0, by simp [loop, hs, hn], Nat.zero_le _, by simp [loop, hs, hn]⟩
      | some t =>
        obtain ⟨k, hk, hbound, he⟩ := ih (count + 1) t
        refine ⟨k + 1, ?_, Nat.add_le_add_right hbound 1, ?_⟩
        · simpa [loop, hs, hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
        · simpa [loop, hs, hn] using Exec.cons (next_sound s t hn) he

/-- What each reported reason guarantees; reaching the budget is not labelled
as a fault and never discards the final state. -/
def Outcome (next : σ → Option σ) (status : σ → Status)
    (limit : Nat) (r : RunResult σ) : Prop :=
  match r.reason with
  | .halted => status r.state = .halted
  | .fault => status r.state = .fault
  | .invalidPC => status r.state = .running ∧ next r.state = none
  | .outOfFuel => status r.state = .running ∧ r.steps = limit

theorem loop_outcome (next : σ → Option σ) (status : σ → Status)
    (fuel count : Nat) (s : σ) :
    Outcome next status (count + fuel) (loop next status fuel count s) := by
  induction fuel generalizing count s with
  | zero => cases hs : status s <;> simp [loop, hs, Outcome]
  | succ fuel ih =>
    cases hs : status s with
    | halted => simp [loop, hs, Outcome]
    | fault => simp [loop, hs, Outcome]
    | running =>
      cases hn : next s with
      | none => simp [loop, hs, hn, Outcome]
      | some t => simpa [loop, hs, hn, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (count + 1) t

theorem runWith_exec {code : Code} {next : σ → Option σ} {status : σ → Status}
    (decode : σ → State w)
    (next_sound : ∀ s t, next s = some t → step code (decode s) = some (decode t))
    (budget : Nat) (s : σ) :
    (runWith next status budget s).steps ≤ budget ∧
      Exec code (runWith next status budget s).steps (decode s)
        (decode (runWith next status budget s).state) := by
  obtain ⟨k, hk, hb, he⟩ := loop_exec (status := status) decode next_sound budget 0 s
  simp only [Nat.zero_add] at hk
  simpa only [runWith, hk] using And.intro hb he

theorem runWith_outcome (next : σ → Option σ) (status : σ → Status)
    (budget : Nat) (s : σ) : Outcome next status budget (runWith next status budget s) := by
  simpa only [Nat.zero_add, runWith] using loop_outcome next status budget 0 s

end Runner

/-- Execute at most `budget` real transitions, preserving state and reason. -/
def run (code : Code) (budget : Nat) (s : State w) : RunResult (State w) :=
  Runner.runWith (step code) State.status budget s

theorem run_exec (code : Code) (budget : Nat) (s : State w) :
    (run code budget s).steps ≤ budget ∧
      Exec code (run code budget s).steps s (run code budget s).state :=
  Runner.runWith_exec id (fun _ _ h => h) budget s

theorem run_outcome (code : Code) (budget : Nat) (s : State w) :
    Runner.Outcome (step code) State.status budget (run code budget s) :=
  Runner.runWith_outcome (step code) State.status budget s

private theorem loop_of_exec {code : Code} {n : Nat} {s t : State w}
    (he : Exec code n s t) (ht : t.status = .halted)
    (budget count : Nat) (hb : n ≤ budget) :
    Runner.loop (step code) State.status budget count s =
      ⟨t, count + n, .halted⟩ := by
  induction he generalizing budget count with
  | refl => cases budget <;> simp [Runner.loop, ht]
  | @cons n s u t hs he ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      have hrun := running_of_step hs
      simpa [Runner.loop, hrun, hs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih ht budget (count + 1) (by omega)

/-- A proof of termination within budget guarantees that the executable runner
actually returns that terminal state and the exact proved transition count. -/
theorem run_of_exec {code : Code} {n budget : Nat} {s t : State w}
    (he : Exec code n s t) (ht : t.status = .halted) (hb : n ≤ budget) :
    run code budget s = ⟨t, n, .halted⟩ := by
  simpa only [run, Runner.runWith, Nat.zero_add] using loop_of_exec he ht budget 0 hb

theorem run_halted_iff {code : Code} {budget : Nat} {s : State w} :
    (run code budget s).reason = .halted ↔
      ∃ t, TerminatesWithin code budget s t := by
  constructor
  · intro h
    obtain ⟨hb, he⟩ := run_exec code budget s
    have ho := run_outcome code budget s
    simp only [Runner.Outcome, h] at ho
    exact ⟨_, _, hb, he, ho⟩
  · rintro ⟨t, n, hb, he, ht⟩
    rw [run_of_exec he ht hb]

theorem run_invalidPC {code : Code} {budget : Nat} {s : State w}
    (h : (run code budget s).reason = .invalidPC) :
    (run code budget s).state.status = .running ∧
      code[(run code budget s).state.pc]? = none := by
  have ho := run_outcome code budget s
  simp only [Runner.Outcome, h] at ho
  refine ⟨ho.1, ?_⟩
  have hn := ho.2
  simp only [step, ho.1, ↓reduceIte] at hn
  cases hf : code[(run code budget s).state.pc]? with
  | none => rfl
  | some i => simp [hf] at hn

end Ram
