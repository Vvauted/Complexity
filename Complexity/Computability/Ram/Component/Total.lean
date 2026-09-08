/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Component.Basic
import Complexity.Computability.Ram.Source.Linking
import Complexity.Computability.Ram.Verification.Observation
import Complexity.Computability.Ram.Verification.Time.Basic

/-!
# Reusable components without a time budget

`Ram.TotalComponent` packages one fixed program with safe total correctness and an
output-size guarantee. Its heap and call-depth bounds are safety capacities;
there is no instruction-count field. Independent components can be linked
before any running-time analysis is supplied.

`Ram.TotalComponent.TimeBoundOn` is a separate conditional bound on actual measured
executions of that program. `Ram.TotalComponent.withTimeBound` combines the two
proofs, preserving the code, interfaces and domain, to obtain the existing
resource-aware `Ram.Component` and its certificate interfaces.
-/

namespace Ram

universe u v

/-- A fixed reusable program with safe total correctness, independently of time. -/
structure TotalComponent {α : Type u} {β : Type v}
    (A : Interface α) (B : Interface β) (f : α → β) (domain : Nat → α → Prop) where
  /-- Number of source registers reserved for the main block and local functions. -/
  locals : Nat
  /-- Local declarations, including any recursive functions. -/
  functions : Program
  /-- The main block, independent of the input and word width. -/
  body : Stmt
  /-- Static validity of the entire module. -/
  valid : LocalCompiler.Valid locals functions body
  /-- Sufficient exclusive upper bound on heap addresses. -/
  heapBound : Nat → Nat
  /-- Sufficient maximum nested call depth, not an execution-time budget. -/
  depthBound : Nat → Nat
  /-- Bound on the mathematical output size for subsequent composition. -/
  sizeBound : Nat → Nat
  /-- The output-size guarantee on every legal input. -/
  size_le : ∀ w x, domain w x → B.size (f x) ≤ sizeBound (A.size x)
  /-- Safe terminating execution, uniformly in word width and surrounding state. -/
  correct : ∀ {w} x, domain w x → ∀ s, A.represents w x s →
    ∀ heapLimit depth, heapBound (A.size x) ≤ heapLimit →
      depthBound (A.size x) ≤ depth →
      ∃ t, Source.SafeExec functions heapLimit depth body s t ∧ B.represents w (f x) t

namespace TotalComponent

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

/-- The same checked compiler used by resource-aware components. -/
def code (p : TotalComponent A B f domain) : Code :=
  LocalCompiler.rawLink p.locals p.functions p.body

theorem compile_eq (p : TotalComponent A B f domain) :
    LocalCompiler.compileChecked p.locals p.functions p.body = some p.code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨p.valid, rfl⟩

/-- Prepare the fixed code for execution without choosing a running-time bound. -/
def executable (p : TotalComponent A B f domain) : Executable :=
  Executable.ofCode p.code

/-- Sufficient heap and private-stack address capacity for the compiled program. -/
def capacity (p : TotalComponent A B f domain) (n : Nat) : Nat :=
  p.heapBound n + p.depthBound n * ABI.frameSize p.locals

/-- Reuse the component's safe total contract in any larger safe environment. -/
theorem contract (p : TotalComponent A B f domain) {w : Nat} (x : α)
    (hx : domain w x) {heapLimit depth : Nat}
    (hh : p.heapBound (A.size x) ≤ heapLimit)
    (hd : p.depthBound (A.size x) ≤ depth) :
    Source.TotalContract p.functions heapLimit depth p.body
      (A.represents w x) (B.represents w (f x)) :=
  fun s hs => p.correct x hx s hs heapLimit depth hh hd

/-- Functional correctness gives an actual halted run, with its duration
existential rather than bounded by a proposed budget. -/
theorem runs_observed (p : TotalComponent A B f domain) {w : Nat} (x : α)
    (hx : domain w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w) (hcapacity : p.capacity (A.size x) < 2 ^ w) :
    ∃ sourceFinal targetFinal steps,
      B.represents w (f x) sourceFinal ∧
      Exec p.code steps
        (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
      targetFinal.status = .halted ∧
      Source.State.Observes (p.heapBound (A.size x)) p.locals sourceFinal targetFinal :=
  (p.contract x hx le_rfl le_rfl).compile_observed p.compile_eq hcode hcapacity hinput

/-- Restrict legal inputs explicitly, preserving the program and all guarantees. -/
def restrict (p : TotalComponent A B f domain) {domain' : Nat → α → Prop}
    (h : ∀ w x, domain' w x → domain w x) : TotalComponent A B f domain' where
  locals := p.locals
  functions := p.functions
  body := p.body
  valid := p.valid
  heapBound := p.heapBound
  depthBound := p.depthBound
  sizeBound := p.sizeBound
  size_le w x hx := p.size_le w x (h w x hx)
  correct x hx := p.correct x (h _ x hx)

/-- Identity preserves the shared representation without executing a body instruction. -/
def id (A : Interface α) (domain : Nat → α → Prop) :
    TotalComponent A A (fun x => x) domain where
  locals := 0
  functions := []
  body := .skip
  valid := by simp [LocalCompiler.Valid, Compiler.Valid, Compiler.CallsValid, Stmt.WellFormed]
  heapBound := fun _ => 0
  depthBound := fun _ => 0
  sizeBound := fun n => n
  size_le _ _ _ := le_rfl
  correct _ _ s hs _ _ _ _ := ⟨s, .skip, hs⟩

/-- A conditional bound on every completed measured execution of the fixed
program. Termination is supplied separately by the component's total contract. -/
def TimeBoundOn (p : TotalComponent A B f domain) (time : Nat → α → Nat) : Prop :=
  ∀ {w} x, domain w x → ∀ heapLimit depth, p.heapBound (A.size x) ≤ heapLimit →
    p.depthBound (A.size x) ≤ depth →
    Source.TimeBound p.locals p.functions heapLimit depth p.body
      (A.represents w x) (fun _ => time w x)

namespace TimeBoundOn

variable {p : TotalComponent A B f domain} {time time' : Nat → α → Nat}

/-- It suffices to analyze the required capacities. Determinism transports
the actual count to larger safe environments, not a user-supplied cost model. -/
theorem of_bound
    (h : ∀ w x, domain w x →
      Source.TimeBound p.locals p.functions (p.heapBound (A.size x))
        (p.depthBound (A.size x)) p.body (A.represents w x) (fun _ => time w x)) :
    p.TimeBoundOn time := by
  intro w x hx H d _ _ s hs steps t execution
  obtain ⟨finish, safe, _⟩ := p.correct x hx s hs _ _ le_rfl le_rfl
  obtain ⟨count, measured⟩ := safe.exists_localMeasured p.locals
  exact (measured.deterministic execution).1 ▸ h w x hx s hs count finish measured

theorem mono (h : p.TimeBoundOn time)
    (hle : ∀ w x, domain w x → time w x ≤ time' w x) : p.TimeBoundOn time' := by
  intro w x hx H d hH hd
  exact (h x hx H d hH hd).mono_budget (fun _ _ => hle w x hx)

/-- Explicit restriction preserves the execution-time proof on retained inputs. -/
theorem restrict (h : p.TimeBoundOn time) {domain' : Nat → α → Prop}
    (hdom : ∀ w x, domain' w x → domain w x) :
    (p.restrict hdom).TimeBoundOn time := by
  intro w x hx H d hH hd
  exact h x (hdom w x hx) H d hH hd

/-- Combine the independent proofs only when a bounded contract is requested. -/
theorem contract (h : p.TimeBoundOn time) {w : Nat} (x : α) (hx : domain w x)
    {heapLimit depth : Nat} (hh : p.heapBound (A.size x) ≤ heapLimit)
    (hd : p.depthBound (A.size x) ≤ depth) :
    Source.Contract p.locals p.functions heapLimit depth p.body
      (A.represents w x) (B.represents w (f x)) (fun _ => time w x) :=
  (p.contract x hx hh hd).with_timeBound (h x hx heapLimit depth hh hd)

end TimeBoundOn

/-- Add a scalar time envelope after proving total correctness. All program,
domain, representation and safety fields remain unchanged. -/
def withTimeBound (p : TotalComponent A B f domain) (time : Nat → Nat)
    (h : p.TimeBoundOn (fun _ x => time (A.size x))) : Component A B f domain where
  locals := p.locals
  functions := p.functions
  body := p.body
  valid := p.valid
  timeBound := time
  heapBound := p.heapBound
  depthBound := p.depthBound
  sizeBound := p.sizeBound
  size_le := p.size_le
  correct x hx s hs _ _ hH hd := h.contract x hx hH hd s hs

@[simp] theorem withTimeBound_code (p : TotalComponent A B f domain) (time : Nat → Nat)
    (h : p.TimeBoundOn (fun _ x => time (A.size x))) :
    (p.withTimeBound time h).code = p.code := rfl

@[simp] theorem withTimeBound_capacity (p : TotalComponent A B f domain) (time : Nat → Nat)
    (h : p.TimeBoundOn (fun _ x => time (A.size x))) (n : Nat) :
    (p.withTimeBound time h).capacity n = p.capacity n := rfl

end TotalComponent

namespace Component

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

/-- Forget time analysis without changing code, domain, representation or safety. -/
def toTotalComponent (p : Component A B f domain) : TotalComponent A B f domain where
  locals := p.locals
  functions := p.functions
  body := p.body
  valid := p.valid
  heapBound := p.heapBound
  depthBound := p.depthBound
  sizeBound := p.sizeBound
  size_le := p.size_le
  correct x hx s hs _ _ hH hd := (p.contract x hx hH hd).total s hs

@[simp] theorem toTotalComponent_code (p : Component A B f domain) :
    p.toTotalComponent.code = p.code := rfl

/-- An existing resource proof bounds every execution of its functional core. -/
theorem toTotalComponent_timeBoundOn (p : Component A B f domain) :
    p.toTotalComponent.TimeBoundOn (fun _ x => p.timeBound (A.size x)) := by
  intro w x hx H d hH hd
  exact (p.contract x hx hH hd).timeBound

@[simp] theorem toTotalComponent_withTimeBound (p : Component A B f domain) :
    p.toTotalComponent.withTimeBound p.timeBound p.toTotalComponent_timeBoundOn = p := by
  cases p
  rfl

end Component

namespace TotalComponent

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

@[simp] theorem withTimeBound_toTotalComponent (p : TotalComponent A B f domain)
    (time : Nat → Nat) (h : p.TimeBoundOn (fun _ x => time (A.size x))) :
    (p.withTimeBound time h).toTotalComponent = p := by
  cases p
  rfl

end TotalComponent
end Ram
