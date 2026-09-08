/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Control
import Complexity.Computability.Ram.Verification.Loop.Logarithmic
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Tactic.Ram.Total

/-!
# A bit-length program with a logarithmic machine budget

This fixed program reads one word, repeatedly divides it by two, increments
an answer register, and writes the answer. Its mathematical result is directly
mathlib's `Nat.clog 2 (input + 1)`, including zero input. There is no separate
bit-length function or input-dependent unrolling in the source language.

The body's functional behavior and instruction bound are proved separately.
Loop correctness is transferred from an ordinary pair of naturals by
`Refines.while_wellFounded`; the result equation is a mathlib logarithm identity,
independent of machine states. A shared dividing-variant rule supplies the
separate time bound of that same execution. The word
adapter proves that division is faithful and the answer increment cannot wrap.

The complete bound includes input, initialization, every evaluated guard,
each division and increment, all back edges, output, the header read and halt.
It counts word-RAM transitions, not bit-operation costs of arithmetic.
-/

namespace Ram.Examples.BitLength

open Source

def condition : Expr := .var 0
def halve : Expr := .bin .udiv (.var 0) (.const 2)
def increment : Expr := .bin .add (.var 1) (.const 1)

def body : Stmt := .seq (.assign 0 halve) (.assign 1 increment)
def loop : Stmt := .while condition body

/-- One program, independent of both the input value and its word width. -/
def main : Stmt :=
  .seq (.read 0) (.seq (.assign 1 (.const 0)) (.seq loop (.write (.var 1))))

def bodyResult (s : Source.State w) : Source.State w :=
  (s.setReg 0 (s.regs 0 / 2)).setReg 1 (s.regs 1 + 1)

@[simp] theorem bodyResult_value (s : Source.State w) :
    (bodyResult s).regs 0 = s.regs 0 / 2 := by simp [bodyResult, Source.State.setReg]

@[simp] theorem bodyResult_answer (s : Source.State w) :
    (bodyResult s).regs 1 = s.regs 1 + 1 := by simp [bodyResult, Source.State.setReg]

@[simp] theorem bodyResult_input (s : Source.State w) :
    (bodyResult s).input = s.input := rfl

@[simp] theorem bodyResult_outputRev (s : Source.State w) :
    (bodyResult s).outputRev = s.outputRev := rfl

/-- The actual assignments implement one division and one answer increment,
without selecting an instruction budget. -/
theorem body_total {H depth : Nat} (s : Source.State w) :
    TotalContract [] H depth body (fun t => t = s) (fun t => t = bodyResult s) := by
  ram_total_vc t ht [body, halve, increment, bodyResult, ht]

/-- These two actual assignments compile to eight primitive instructions. -/
theorem body_contract {H depth : Nat} (s : Source.State w) :
    Contract 2 [] H depth body (fun t => t = s)
      (fun t => t = bodyResult s) (fun _ => 8) := by
  ram_vc t ht [body, halve, increment, bodyResult, ht]

def Invariant (input : Nat) (s : Source.State w) : Prop :=
  (s.regs 1).toNat + Nat.clog 2 ((s.regs 0).toNat + 1) = Nat.clog 2 (input + 1) ∧
  s.input = [] ∧ s.outputRev = []

def InputReady (input : Nat) (s : Source.State w) : Prop :=
  s.input = [BitVec.ofNat w input] ∧ s.outputRev = []

def CountReady (input : Nat) (s : Source.State w) : Prop :=
  (s.regs 0).toNat = input ∧ s.input = [] ∧ s.outputRev = []

def AnswerReady (input : Nat) (s : Source.State w) : Prop :=
  (s.regs 1).toNat = Nat.clog 2 (input + 1) ∧ s.input = [] ∧ s.outputRev = []

def Post (input : Nat) (s : Source.State w) : Prop :=
  s.output = [BitVec.ofNat w (Nat.clog 2 (input + 1))] ∧ s.input = []

/-- The result bound uses mathlib's logarithm/power adjunction directly. -/
theorem answer_le_width {input : Nat} (hinput : input < 2 ^ w) :
    Nat.clog 2 (input + 1) ≤ w :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by omega)

theorem answer_fits {input : Nat} (hinput : input < 2 ^ w) :
    Nat.clog 2 (input + 1) < 2 ^ w :=
  lt_of_le_of_lt (answer_le_width hinput) Nat.lt_two_pow_self

/-- The mathematical state consists of the remaining value and accumulated answer. -/
def modelStep (state : Nat × Nat) : Nat × Nat := (state.1 / 2, state.2 + 1)

/-- The final answer, expressed directly with mathlib's logarithm. -/
def modelResult (state : Nat × Nat) : Nat := state.2 + Nat.clog 2 (state.1 + 1)

/-- The functional invariant is ordinary arithmetic, without registers or words. -/
theorem modelResult_step (state : Nat × Nat) (positive : 0 < state.1) :
    modelResult (modelStep state) = modelResult state := by
  have hlog := Nat.clog_div_succ_add_one (by decide : 1 < 2) positive
  dsimp [modelResult, modelStep]
  omega

/-- The two live registers represent an ordinary pair; I/O is preserved. -/
def ModelRep (state : Nat × Nat) (s : Source.State w) : Prop :=
  (s.regs 0).toNat = state.1 ∧ (s.regs 1).toNat = state.2 ∧
    s.input = [] ∧ s.outputRev = []

private theorem positive_value (s : Source.State w) (hz : s.eval condition ≠ 0) :
    0 < (s.regs 0).toNat := by
  have hne : (s.regs 0).toNat ≠ 0 := fun h => hz ((Word.toNat_eq_zero_iff _).mp h)
  omega

/-- This is a statement about the concrete word division, not an assumed
decrease of a mathematical ghost counter. Width at least two represents the
divisor two faithfully. -/
theorem bodyResult_div (hw : 2 ≤ w) (s : Source.State w) :
    ((bodyResult s).regs 0).toNat = (s.regs 0).toNat / 2 := by
  have htwoFit : 2 < 2 ^ w := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  have htwo : (2 : Word w).toNat = 2 := Word.ofNat_toNat_of_lt htwoFit
  rw [bodyResult_value]
  change (BinOp.eval .udiv (s.regs 0) 2).toNat = _
  rw [BinOp.eval_udiv_toNat, htwo]

/-- The word adapter proves the real body implements the mathematical step.
Its only arithmetic-specific obligations are faithful division and no wrap. -/
theorem bodyResult_rep (hw : 2 ≤ w) {state : Nat × Nat}
    (positive : 0 < state.1) (fits : modelResult state < 2 ^ w)
    (s : Source.State w) (represented : ModelRep state s) :
    ModelRep (modelStep state) (bodyResult s) := by
  have hlogpos := Nat.clog_pos (by decide : 1 < 2)
    (show 1 < state.1 + 1 from by omega)
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one (by omega)
  have hanswerFit : (s.regs 1).toNat + (1 : Word w).toNat < 2 ^ w := by
    rw [represented.2.1, hone]
    dsimp [modelResult] at fits
    omega
  refine ⟨?_, ?_, represented.2.2⟩
  · change ((bodyResult s).regs 0).toNat = state.1 / 2
    rw [bodyResult_div hw s, represented.1]
  · change ((bodyResult s).regs 1).toNat = state.2 + 1
    rw [bodyResult_answer, BitVec.toNat_add_of_lt hanswerFit, hone, represented.2.1]

/-- One positive iteration preserves the answer equation. A positive remaining
logarithm guarantees room for the actual increment before it is executed. -/
theorem bodyResult_preserves {input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w)
    (s : Source.State w) (hs : Invariant input s) (hz : s.eval condition ≠ 0) :
    Invariant input (bodyResult s) ∧
      ((bodyResult s).regs 0).toNat ≤ (s.regs 0).toNat / 2 := by
  let state : Nat × Nat := ((s.regs 0).toNat, (s.regs 1).toNat)
  have hp : 0 < state.1 := positive_value s hz
  have hfit : modelResult state < 2 ^ w := by
    change (s.regs 1).toNat + Nat.clog 2 ((s.regs 0).toNat + 1) < 2 ^ w
    rw [hs.1]
    exact answer_fits hinput
  have represented := bodyResult_rep hw hp hfit s ⟨rfl, rfl, hs.2⟩
  refine ⟨⟨?_, represented.2.2⟩, le_of_eq represented.1⟩
  simpa only [modelResult, represented.1, represented.2.1] using
    (modelResult_step state hp).trans hs.1

/-- Functional loop verification uses a natural-pair model and the ordinary
strict order on its remaining value. It has no time budget or execution tree. -/
theorem loop_refines {H depth : Nat} (hw : 2 ≤ w) :
    Refines (w := w) [] H depth loop
      (fun state s => ModelRep state s ∧ modelResult state < 2 ^ w)
      (fun answer s => (s.regs 1).toNat = answer ∧ s.input = [] ∧ s.outputRev = [])
      modelResult := by
  apply Refines.while_wellFounded (fun state => modelResult state < 2 ^ w)
    (fun state => 0 < state.1) modelStep modelResult (measure Prod.fst).wf
  · intro state s represented fits
    trivial
  · intro state s represented fits
    constructor
    · intro hz
      exact represented.1 ▸ positive_value s hz
    · intro positive hz
      have hzero : (s.regs 0).toNat = 0 := (Word.toNat_eq_zero_iff _).mpr hz
      have hvalue := represented.1
      omega
  · intro state fits positive s represented
    apply (body_total s).mono_post ?_ s rfl
    intro t ht
    subst t
    exact bodyResult_rep hw positive fits s represented
  · intro state fits positive
    simpa only [modelResult_step state positive] using fits
  · intro state fits positive
    exact Nat.div_lt_self positive (by decide)
  · intro state fits positive
    exact modelResult_step state positive
  · intro state s represented fits finished
    have hzero : state.1 = 0 := by omega
    refine ⟨?_, represented.2.2⟩
    simpa only [modelResult, hzero, Nat.zero_add, Nat.clog_one_right, Nat.add_zero] using
      represented.2.1

/-- Recover the original invariant-based functional API from the model refinement. -/
theorem loop_total {H depth input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w) :
    TotalContract (w := w) [] H depth loop (Invariant input) (AnswerReady input) := by
  intro s hs
  have hfit : modelResult ((s.regs 0).toNat, (s.regs 1).toNat) < 2 ^ w := by
    change (s.regs 1).toNat + Nat.clog 2 ((s.regs 0).toNat + 1) < 2 ^ w
    rw [hs.1]
    exact answer_fits hinput
  obtain ⟨t, execution, answer, io⟩ :=
    loop_refines hw ((s.regs 0).toNat, (s.regs 1).toNat) s ⟨⟨rfl, rfl, hs.2⟩, hfit⟩
  exact ⟨t, execution, answer.trans hs.1, io⟩

/-- The cost proof is independent of the loop's final-answer specification.
The shared logarithmic rule accounts for every guard, body and back-edge. -/
theorem loop_timeBound {H depth input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w) :
    TimeBound (w := w) 2 [] H depth loop (Invariant input)
      (fun _ => 11 * Nat.clog 2 (input + 1) + 2) := by
  have cost : TimeBound (w := w) 2 [] H depth loop (Invariant input)
      (fun s => Nat.clog 2 ((s.regs 0).toNat + 1) * 11 + 2) := by
    apply TimeBound.while_div 2 (by decide) (Invariant input)
      (fun s => (s.regs 0).toNat) 8
    · intro s _ hz
      exact positive_value s hz
    · intro s hs
      obtain ⟨t, execution, result⟩ := body_total s s rfl
      subst t
      exact ⟨bodyResult s, execution, bodyResult_preserves hw hinput s hs.1 hs.2⟩
    · intro s hs steps t hx
      exact (body_contract s).timeBound s rfl steps t hx
  apply cost.mono_budget
  intro s hs
  have hsum := hs.1
  omega

/-- The original exact public budget combines separate model correctness
and machine-time proofs for the same loop. -/
theorem loop_contract {H depth input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w) :
    Contract (w := w) 2 [] H depth loop (Invariant input) (AnswerReady input)
      (fun _ => 11 * Nat.clog 2 (input + 1) + 2) :=
  (loop_total hw hinput).with_timeBound (loop_timeBound hw hinput)

/-- The I/O adapters and initialization are included in the source contract;
no host-side initialization or uncharged output conversion is assumed. -/
theorem main_contract {H depth input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w) :
    Contract (w := w) 2 [] H depth main (InputReady input) (Post input)
      (fun _ => 11 * Nat.clog 2 (input + 1) + 7) := by
  have hr : Contract (w := w) 2 [] H depth (.read 0) (InputReady input)
      (CountReady input) (fun _ => 1) := by
    ram_vc s hs [CountReady, hs.1, hs.2, Word.ofNat_toNat_of_lt hinput]
  have hi : Contract (w := w) 2 [] H depth (.assign 1 (.const 0)) (CountReady input)
      (Invariant input) (fun _ => 2) := by
    ram_vc s hs [Invariant, hs.1, hs.2.1, hs.2.2]
  have ho : Contract (w := w) 2 [] H depth (.write (.var 1)) (AnswerReady input)
      (Post input) (fun _ => 2) := by
    ram_vc s hs [Post, hs.2.1, hs.2.2]
    have hword : s.regs 1 = BitVec.ofNat w (Nat.clog 2 (input + 1)) := by
      rw [← hs.1, Word.ofNat_toNat_self]
    ram_simp [hword]
  have h := hr.seq_const (hi.seq_const ((loop_contract hw hinput).seq_const ho))
  apply h.mono_budget
  intro s hs
  omega

def machine : Code := LocalCompiler.rawLink 2 [] main

theorem main_valid : LocalCompiler.Valid 2 [] main := by
  simp [LocalCompiler.Valid, Compiler.Valid, main, loop, body, condition, halve, increment,
    Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]

theorem checked_machine : LocalCompiler.compileChecked 2 [] main = some machine :=
  LocalCompiler.compileChecked_some_iff.mpr ⟨main_valid, rfl⟩

theorem machine_code_size : machine.length = 18 := rfl

/-- Full actual-machine logarithmic time, including the header read and halt.
The empty source heap is represented by the counted zero boundary header. -/
theorem machine_correct {input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w)
    (hcodefit : 18 < 2 ^ w) :
    ∃ finish,
      Ram.TerminatesWithin machine (11 * Nat.clog 2 (input + 1) + 9)
        (Ram.State.initial [0, BitVec.ofNat w input]) finish ∧
      finish.output = [BitVec.ofNat w (Nat.clog 2 (input + 1))] ∧ finish.input = [] := by
  have hc : machine.length < 2 ^ w := by rw [machine_code_size]; exact hcodefit
  have hs : 0 + 0 * ABI.frameSize 2 < 2 ^ w := by simp
  obtain ⟨sourceFinal, finish, hp, ht, hout, hin⟩ :=
    (main_contract (H := 0) (depth := 0) hw hinput).compile checked_machine hc hs ⟨rfl, rfl⟩
  refine ⟨finish, ?_, hout.trans hp.1, hin.trans hp.2⟩
  simpa only [Nat.add_assoc] using ht

/-- Decoding the emitted word returns the actual natural ceiling logarithm,
not merely a modular encoding of an out-of-range answer. -/
theorem machine_correct_decoded {input : Nat} (hw : 2 ≤ w) (hinput : input < 2 ^ w)
    (hcodefit : 18 < 2 ^ w) :
    ∃ finish,
      Ram.TerminatesWithin machine (11 * Nat.clog 2 (input + 1) + 9)
        (Ram.State.initial [0, BitVec.ofNat w input]) finish ∧
      finish.output.map BitVec.toNat = [Nat.clog 2 (input + 1)] ∧ finish.input = [] := by
  obtain ⟨finish, ht, hout, hin⟩ := machine_correct hw hinput hcodefit
  refine ⟨finish, ht, ?_, hin⟩
  rw [hout]
  simp only [List.map_cons, List.map_nil, Word.ofNat_toNat_of_lt (answer_fits hinput)]

end Ram.Examples.BitLength
