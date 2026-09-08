/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Executable
import Complexity.Computability.Ram.Problem.Basic
import Complexity.Computability.Ram.Verification.Contract
import Complexity.Computability.Ram.Verification.Execution

/-!
# Reusable algorithms with data interfaces and resource bounds

An `Interface` describes mathematical data in a source state. A `Component`
contains a fixed structured program, its local functions, and a total-correctness
proof reusable in every sufficiently large heap and call stack. The interface,
function, and legal input predicate are parameters, not choices hidden in the
correctness proof.

Time bounds count the instructions of the verified compiler. `heapBound` is a
sufficient heap address-space capacity, not the number of occupied words;
`depthBound` bounds nested calls. The separate `sizeBound` controls the size of
the result passed to the next component.

## Main declarations

- `Component.contract`: reuse a component inside a larger proof.
- `Component.runs`: obtain execution of its complete compiled RAM program.
- `Component.certificate`: discharge a previously fixed problem specification.

Representations and encodings are specifications. They must describe data, not
perform an uncharged part of the requested algorithm. Composition uses shared
state representations; an encoding conversion must be an executable component.
-/

namespace Ram

universe u v

/-- A problem-owned representation of mathematical data and its size measure. -/
structure Interface (α : Type u) where
  /-- The input-size convention used by resource bounds. -/
  size : α → Nat
  /-- The relation between mathematical data and the program's visible state. -/
  represents : ∀ w, α → Source.State w → Prop

/-- A fixed program with correctness and resource proofs on its stated domain. -/
structure Component {α : Type u} {β : Type v}
    (A : Interface α) (B : Interface β) (f : α → β) (domain : Nat → α → Prop) where
  /-- Number of source registers reserved for the main block and local functions. -/
  locals : Nat
  /-- Local declarations, including any recursive functions. -/
  functions : Program
  /-- The main block, independent of the input and word width. -/
  body : Stmt
  /-- Static validity of the entire module. -/
  valid : LocalCompiler.Valid locals functions body
  /-- Bound on actual compiled body transitions. -/
  timeBound : Nat → Nat
  /-- Sufficient exclusive upper bound on heap addresses. -/
  heapBound : Nat → Nat
  /-- Sufficient maximum nested call depth. -/
  depthBound : Nat → Nat
  /-- Bound on the mathematical output size. -/
  sizeBound : Nat → Nat
  /-- The output-size guarantee on every legal input. -/
  size_le : ∀ w x, domain w x → B.size (f x) ≤ sizeBound (A.size x)
  /-- Total execution, uniformly in the word width and surrounding state. -/
  correct : ∀ {w} x, domain w x → ∀ s, A.represents w x s →
    ∀ heapLimit depth, heapBound (A.size x) ≤ heapLimit →
      depthBound (A.size x) ≤ depth →
      ∃ steps t,
        Source.LocalMeasuredExec locals functions heapLimit depth body steps s t ∧
        B.represents w (f x) t ∧ steps ≤ timeBound (A.size x)

namespace Component

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

/-- Compile a verified module to one complete RAM instruction list. -/
def code (p : Component A B f domain) : Code :=
  LocalCompiler.rawLink p.locals p.functions p.body

theorem compile_eq (p : Component A B f domain) :
    LocalCompiler.compileChecked p.locals p.functions p.body = some p.code :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨p.valid, rfl⟩

/-- Prepare the same code for the verified fast runner. -/
def executable (p : Component A B f domain) : Executable :=
  Executable.ofCode p.code

/-- The whole program includes one header read and one halt transition. -/
def totalTime (p : Component A B f domain) (n : Nat) : Nat := p.timeBound n + 2

/-- Include the compiler's sufficient stack reservation in the address capacity. -/
def capacity (p : Component A B f domain) (n : Nat) : Nat :=
  p.heapBound n + p.depthBound n * ABI.frameSize p.locals

/-- Import a module's proof as an ordinary contract with a ghost mathematical input. -/
theorem contract (p : Component A B f domain) {w : Nat} (x : α)
    (hx : domain w x) {heapLimit depth : Nat}
    (hh : p.heapBound (A.size x) ≤ heapLimit)
    (hd : p.depthBound (A.size x) ≤ depth) :
    Source.Contract p.locals p.functions heapLimit depth p.body
      (A.represents w x) (B.represents w (f x)) (fun _ => p.timeBound (A.size x)) :=
  fun s hs => p.correct x hx s hs heapLimit depth hh hd

/-- Execution of a compiled component, with the actual halted heap and I/O.
The target's private stack is not part of the source representation. -/
theorem runs (p : Component A B f domain) {w : Nat} (x : α)
    (hx : domain w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w) (hcapacity : p.capacity (A.size x) < 2 ^ w) :
    ∃ sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧
      TerminatesWithin p.code (p.totalTime (A.size x))
        (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
      HeapEqBelow (p.heapBound (A.size x)) sourceFinal.mem targetFinal.mem ∧
      targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  exact (p.contract x hx (Nat.le_refl _) (Nat.le_refl _)).compile_heap
    p.compile_eq hcode hcapacity hinput

/-- The same complete execution retains local register results as well as heap
and I/O. Compiler-reserved registers and private stack words are excluded. -/
theorem runs_observed (p : Component A B f domain) {w : Nat} (x : α)
    (hx : domain w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w) (hcapacity : p.capacity (A.size x) < 2 ^ w) :
    ∃ sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧
      TerminatesWithin p.code (p.totalTime (A.size x))
        (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
      Source.State.Observes (p.heapBound (A.size x)) p.locals sourceFinal targetFinal := by
  exact (p.contract x hx (Nat.le_refl _) (Nat.le_refl _)).compile_observed
    p.compile_eq hcode hcapacity hinput

/-- Strengthen a component's domain without changing its program or resource bounds. -/
def restrict (p : Component A B f domain) {domain' : Nat → α → Prop}
    (h : ∀ w x, domain' w x → domain w x) : Component A B f domain' where
  locals := p.locals
  functions := p.functions
  body := p.body
  valid := p.valid
  timeBound := p.timeBound
  heapBound := p.heapBound
  depthBound := p.depthBound
  sizeBound := p.sizeBound
  size_le w x hx := p.size_le w x (h w x hx)
  correct x hx := p.correct x (h _ x hx)

/-- Enlarge proved resource bounds without redoing the program proof. -/
def weaken (p : Component A B f domain)
    (time heap depth size : Nat → Nat)
    (ht : ∀ n, p.timeBound n ≤ time n) (hh : ∀ n, p.heapBound n ≤ heap n)
    (hd : ∀ n, p.depthBound n ≤ depth n) (hs : ∀ n, p.sizeBound n ≤ size n) :
    Component A B f domain where
  locals := p.locals
  functions := p.functions
  body := p.body
  valid := p.valid
  timeBound := time
  heapBound := heap
  depthBound := depth
  sizeBound := size
  size_le w x hx := Nat.le_trans (p.size_le w x hx) (hs _)
  correct x hx s hrep H d hH hd' := by
    obtain ⟨steps, t, he, hr, hb⟩ := p.correct x hx s hrep H d
      (Nat.le_trans (hh _) hH) (Nat.le_trans (hd _) hd')
    exact ⟨steps, t, he, hr, Nat.le_trans hb (ht _)⟩

/-- Identity on a shared representation performs no body instructions. The complete
compiled executable still pays for its header read and halt. -/
def id (A : Interface α) (domain : Nat → α → Prop) :
    Component A A (fun x => x) domain where
  locals := 0
  functions := []
  body := .skip
  valid := by simp [LocalCompiler.Valid, Compiler.Valid, Compiler.CallsValid, Stmt.WellFormed]
  timeBound := fun _ => 0
  heapBound := fun _ => 0
  depthBound := fun _ => 0
  sizeBound := fun n => n
  size_le _ _ _ := Nat.le_refl _
  correct _ _ s hs _ _ _ _ := ⟨0, s, .skip, hs, Nat.le_refl _⟩

/-- Export to a problem fixed by the caller. In particular, compilation-capacity
conditions must hold for every input accepted by that problem; this constructor
does not remove inconvenient inputs from the problem's domain. -/
def certificate {α : Type} {A : Interface α} {f : α → β}
    {domain : Nat → α → Prop} (p : Component A B f domain) (problem : Problem α)
    (input : ∀ w, α → List (Word w))
    (hsize : problem.size = A.size)
    (hencode : ∀ w x, problem.encode w x =
      BitVec.ofNat w (p.heapBound (A.size x)) :: input w x)
    (hdomain : ∀ w x, problem.admissible w x → domain w x)
    (hinput : ∀ w x, problem.admissible w x →
      A.represents w x (Source.State.initial (input w x)))
    (hcode : ∀ w x, problem.admissible w x → p.code.length < 2 ^ w)
    (hcapacity : ∀ w x, problem.admissible w x → p.capacity (A.size x) < 2 ^ w)
    (hpost : ∀ w x, problem.admissible w x → ∀ s t,
      B.represents w (f x) s → HeapEqBelow (p.heapBound (A.size x)) s.mem t.mem →
      t.output = s.output → t.input = s.input → problem.post w x t) :
    Certificate problem p.totalTime where
  code := p.code
  verified w x hx := by
    obtain ⟨s, t, hr, he, hm, ho, hi⟩ := p.runs x (hdomain w x hx)
      (input w x) (hinput w x hx) (hcode w x hx) (hcapacity w x hx)
    refine ⟨t, ?_, hpost w x hx s t hr hm ho hi⟩
    simpa only [hsize, hencode] using he

/-- A fixed-problem certificate may observe all of the component's local
registers, not just its output stream. The observation is of the same halted run. -/
def certificate_observed {α : Type} {A : Interface α} {f : α → β}
    {domain : Nat → α → Prop} (p : Component A B f domain) (problem : Problem α)
    (input : ∀ w, α → List (Word w))
    (hsize : problem.size = A.size)
    (hencode : ∀ w x, problem.encode w x =
      BitVec.ofNat w (p.heapBound (A.size x)) :: input w x)
    (hdomain : ∀ w x, problem.admissible w x → domain w x)
    (hinput : ∀ w x, problem.admissible w x →
      A.represents w x (Source.State.initial (input w x)))
    (hcode : ∀ w x, problem.admissible w x → p.code.length < 2 ^ w)
    (hcapacity : ∀ w x, problem.admissible w x → p.capacity (A.size x) < 2 ^ w)
    (hpost : ∀ w x, problem.admissible w x → ∀ s t,
      B.represents w (f x) s →
      Source.State.Observes (p.heapBound (A.size x)) p.locals s t → problem.post w x t) :
    Certificate problem p.totalTime where
  code := p.code
  verified w x hx := by
    obtain ⟨s, t, hr, he, ho⟩ := p.runs_observed x (hdomain w x hx)
      (input w x) (hinput w x hx) (hcode w x hx) (hcapacity w x hx)
    refine ⟨t, ?_, hpost w x hx s t hr ho⟩
    simpa only [hsize, hencode] using he

end Component
end Ram
