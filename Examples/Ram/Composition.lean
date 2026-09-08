/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Component.Composition
import Complexity.Computability.Ram.Component.Contract
import Complexity.Computability.Ram.Verification.Basic

/-!
# Linking two independent function modules between I/O adapters

The increment and doubling modules each call function number zero in their
own one-function table. Their proofs apply to arbitrary source states meeting
the shared register interface. Composition relocates the second module and
reuses both proofs; neither module knows the eventual function numbering.

Input decoding and output encoding are ordinary charged RAM read/write
components. The shared interface holds one natural number in register zero,
with an explicit word-fit condition. The legal domain prevents overflow in
both arithmetic functions. The final result is the natural number `2 * (x + 1)`.

The size convention is explicitly the numeric magnitude `size x = x`.
These are fixed-word RAM transition bounds, not claims about bit complexity.
Polynomial certificates and their composition come from the public component
API; the complete program additionally has the concrete bound of 55 steps.
The four `Ram.TotalComponent` packages and their composition are defined from safe
total contracts first. Separate time proofs then attach bounds to the same code.
-/

namespace Ram.Examples.Composition

open Source

def inputInterface : Interface Nat where
  size := fun x => x
  represents w x s := s.input = [BitVec.ofNat w x] ∧ s.outputRev = []

def registerInterface : Interface Nat where
  size := fun x => x
  represents w x s :=
    x < 2 ^ w ∧ s.regs 0 = BitVec.ofNat w x ∧ s.input = [] ∧ s.outputRev = []

def outputInterface : Interface Nat where
  size := fun x => x
  represents w x s :=
    x < 2 ^ w ∧ s.output = [BitVec.ofNat w x] ∧ s.input = []

def legal (w x : Nat) : Prop := 2 * (x + 1) < 2 ^ w
def incrementDomain (w x : Nat) : Prop := x + 1 < 2 ^ w
def doubleDomain (w x : Nat) : Prop := 2 * x < 2 ^ w

def incrementFunction : Func where
  params := 1
  locals := 1
  body := .assign 0 (.bin .add (.var 0) (.const 1))
  result := .var 0

def doubleFunction : Func where
  params := 1
  locals := 1
  body := .assign 0 (.bin .mul (.const 2) (.var 0))
  result := .var 0

/-- Each module has this same local main block; its function zero is resolved
against that module's own declarations until `Component.comp` links them. -/
def invoke : Stmt := .call 0 0 [.var 0]

/-- Reading establishes the shared representation without a time budget. -/
theorem read_total {w H depth x : Nat} (hx : legal w x) :
    TotalContract [] H depth (.read 0) (inputInterface.represents w x)
      (registerInterface.represents w x) := by
  have hfit : x < 2 ^ w := by unfold legal at hx; omega
  apply Source.Verification.verify_total
  intro s hs
  obtain ⟨hin, hout⟩ := hs
  simp [Source.Verification.TotalWP.read_iff, hin, registerInterface,
    Source.State.setReg, hfit, hout]

/-- Writing preserves the mathematical value without a time budget. -/
theorem write_total {w H depth x : Nat} :
    TotalContract [] H depth (.write (.var 0)) (registerInterface.represents w x)
      (outputInterface.represents w x) := by
  apply Source.Verification.verify_total
  intro s hs
  obtain ⟨hfit, hreg, hin, hout⟩ := hs
  simp [Source.Verification.TotalWP.write_iff, outputInterface, Expr.ReadsBelow,
    Source.State.eval, Expr.eval, Source.State.output, hfit, hreg, hin, hout]

/-- The arithmetic result uses safe call and assignment rules, not a fuel calculation. -/
theorem increment_total {w H depth x : Nat}
    (hx : incrementDomain w x) (hd : 1 ≤ depth) :
    TotalContract [incrementFunction] H depth invoke (registerInterface.represents w x)
      (registerInterface.represents w (x + 1)) := by
  intro s hs
  have body := SafeExec.assign (program := [incrementFunction]) (heapLimit := H)
    (d := 0) (s := s.enter ([Expr.var 0].map s.eval)) (dst := 0)
    (value := Expr.bin .add (.var 0) (.const 1)) (by simp [Expr.ReadsBelow])
  have execution := SafeExec.call (f := incrementFunction) (dst := 0) (fn := 0)
    (args := [Expr.var 0]) rfl rfl (by decide)
    (by simp [Expr.ReadsBelow]) body (by simp [incrementFunction, Expr.ReadsBelow])
  refine ⟨_, execution.mono hd, ?_⟩
  obtain ⟨_, hreg, hin, hout⟩ := hs
  simp [registerInterface, incrementFunction, Source.State.leave, Source.State.enter,
    Source.State.setReg, Source.State.eval, Expr.eval, BinOp.eval, hreg, hin, hout,
    BitVec.ofNat_add, incrementDomain] at hx ⊢
  exact hx

/-- Doubling has its own independent safe total proof over its local function table. -/
theorem double_total {w H depth x : Nat}
    (hx : doubleDomain w x) (hd : 1 ≤ depth) :
    TotalContract [doubleFunction] H depth invoke (registerInterface.represents w x)
      (registerInterface.represents w (2 * x)) := by
  intro s hs
  have body := SafeExec.assign (program := [doubleFunction]) (heapLimit := H)
    (d := 0) (s := s.enter ([Expr.var 0].map s.eval)) (dst := 0)
    (value := Expr.bin .mul (.const 2) (.var 0)) (by simp [Expr.ReadsBelow])
  have execution := SafeExec.call (f := doubleFunction) (dst := 0) (fn := 0)
    (args := [Expr.var 0]) rfl rfl (by decide)
    (by simp [Expr.ReadsBelow]) body (by simp [doubleFunction, Expr.ReadsBelow])
  refine ⟨_, execution.mono hd, ?_⟩
  obtain ⟨_, hreg, hin, hout⟩ := hs
  simp [registerInterface, doubleFunction, Source.State.leave, Source.State.enter,
    Source.State.setReg, Source.State.eval, Expr.eval, BinOp.eval, hreg, hin, hout,
    BitVec.ofNat_mul, doubleDomain] at hx ⊢
  exact hx

/-- The input adapter is packaged before its time analysis. -/
def readerTotal : TotalComponent inputInterface registerInterface (fun x => x) legal :=
  .ofNamed ⟨1, [], .read 0⟩ (fun _ => 0) (fun _ => 0) (fun n => n)
    (by simp [Named.Bundle.program, LocalCompiler.Valid, Compiler.Valid,
      Stmt.WellFormed, Compiler.CallsValid])
    (fun _ _ _ => le_rfl) (fun _ _ hx => read_total hx)

/-- The increment module has safe total correctness and output size, but no time field. -/
def incrementTotal : TotalComponent registerInterface registerInterface
    (fun x => x + 1) incrementDomain :=
  .ofNamed ⟨1, [("increment", incrementFunction)], invoke⟩
    (fun _ => 0) (fun _ => 1) (fun n => n + 1)
    (by simp [Named.Bundle.program, LocalCompiler.Valid, Compiler.Valid, invoke,
      incrementFunction, Func.WellFormed, Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid])
    (fun _ _ _ => le_rfl) (fun _ _ hx => increment_total hx le_rfl)

/-- Doubling is packaged independently with the same shared representation. -/
def doubleTotal : TotalComponent registerInterface registerInterface
    (fun x => 2 * x) doubleDomain :=
  .ofNamed ⟨1, [("double", doubleFunction)], invoke⟩
    (fun _ => 0) (fun _ => 1) (fun n => 2 * n)
    (by simp [Named.Bundle.program, LocalCompiler.Valid, Compiler.Valid, invoke,
      doubleFunction, Func.WellFormed, Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid])
    (fun _ _ _ => le_rfl) (fun _ _ hx => double_total hx le_rfl)

/-- The output adapter also needs no time bound to expose its functional contract. -/
def writerTotal : TotalComponent registerInterface outputInterface (fun x => x)
    (fun _ _ => True) :=
  .ofNamed ⟨1, [], .write (.var 0)⟩ (fun _ => 0) (fun _ => 0) (fun n => n)
    (by simp [Named.Bundle.program, LocalCompiler.Valid, Compiler.Valid,
      Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid])
    (fun _ _ _ => le_rfl) (fun _ _ _ => write_total)

theorem incrementDomain_of_legal {w x : Nat} (hx : legal w x) : incrementDomain w x := by
  unfold legal at hx
  unfold incrementDomain
  omega

/-- Link the whole safe, terminating pipeline before choosing any instruction budget. -/
def totalPipeline := writerTotal.comp
  ((doubleTotal.comp
    (incrementTotal.restrict (fun _ _ hx => incrementDomain_of_legal hx))
    (fun _ _ hx => hx)).comp readerTotal (fun _ _ hx => hx)) (fun _ _ _ => trivial)

theorem read_contract {w H depth x : Nat} (hx : legal w x) :
    Contract 1 [] H depth (.read 0) (inputInterface.represents w x)
      (registerInterface.represents w x) (fun _ => 1) := by
  have hfit : x < 2 ^ w := by unfold legal at hx; omega
  apply Source.Verification.verify
  intro s hs
  obtain ⟨hin, hout⟩ := hs
  simp only [Source.Verification.WP.read_iff, hin]
  simp [registerInterface, LocalCompiler.stmtSize, LocalCompiler.compileStmt,
    Source.State.setReg, hfit, hout]

theorem write_contract {w H depth x : Nat} :
    Contract 1 [] H depth (.write (.var 0)) (registerInterface.represents w x)
      (outputInterface.represents w x) (fun _ => 2) := by
  apply Source.Verification.verify
  intro s hs
  obtain ⟨hfit, hreg, hin, hout⟩ := hs
  simp [Source.Verification.WP.write_iff, outputInterface, Expr.ReadsBelow,
    LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile,
    Source.State.eval, Expr.eval, Source.State.output, hfit, hreg, hin, hout]

/-- This independent proof uses only its own function table. The function's
assignment is proved by WP substitution and the call by the public call rule. -/
theorem increment_contract {w H depth x : Nat}
    (hx : incrementDomain w x) (hd : 1 ≤ depth) :
    Contract 1 [incrementFunction] H depth invoke (registerInterface.represents w x)
      (registerInterface.represents w (x + 1)) (fun _ => 25) := by
  have hcall := Contract.call (n := 1) (program := [incrementFunction])
    (heapLimit := H) (depth := 0) (dst := 0) (fn := 0) (args := [Expr.var 0])
    (P := registerInterface.represents w x) (Q := registerInterface.represents w (x + 1))
    (bodyBound := fun _ => 4)
    (show [incrementFunction][0]? = some incrementFunction from rfl) rfl (by decide)
    (show ∀ s, registerInterface.represents w x s →
      ∀ arg ∈ [Expr.var 0], arg.ReadsBelow H s.regs s.mem from by
      intro s hs
      simp [Expr.ReadsBelow])
    (show ∀ caller, registerInterface.represents w x caller →
      Contract 1 [incrementFunction] H 0 incrementFunction.body
        (fun s => s = caller.enter ([Expr.var 0].map caller.eval))
        (fun finish => incrementFunction.result.ReadsBelow H finish.regs finish.mem ∧
          registerInterface.represents w (x + 1)
            (caller.leave finish 0 incrementFunction.result)) (fun _ => 4) from by
      intro caller hcaller
      obtain ⟨_, hreg, hin, hout⟩ := hcaller
      apply Source.Verification.verify
      intro entered he
      subst entered
      simp [incrementFunction, Source.Verification.WP.assign_iff, registerInterface,
        Expr.ReadsBelow, LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile,
        Source.State.leave, Source.State.enter, Source.State.setReg, Source.State.eval,
        Expr.eval, BinOp.eval, hreg, hin, hout, BitVec.ofNat_add, incrementDomain] at hx ⊢
      exact hx)
  simpa [invoke, ABI.callPrefixLocals_length_eq, ABI.returnCodeLocals_length,
    incrementFunction, Expr.compile] using hcall.mono_depth hd

/-- The second module also uses function zero, without referring to the
increment module or its eventual position in the linked table. -/
theorem double_contract {w H depth x : Nat}
    (hx : doubleDomain w x) (hd : 1 ≤ depth) :
    Contract 1 [doubleFunction] H depth invoke (registerInterface.represents w x)
      (registerInterface.represents w (2 * x)) (fun _ => 25) := by
  have hcall := Contract.call (n := 1) (program := [doubleFunction])
    (heapLimit := H) (depth := 0) (dst := 0) (fn := 0) (args := [Expr.var 0])
    (P := registerInterface.represents w x) (Q := registerInterface.represents w (2 * x))
    (bodyBound := fun _ => 4)
    (show [doubleFunction][0]? = some doubleFunction from rfl) rfl (by decide)
    (show ∀ s, registerInterface.represents w x s →
      ∀ arg ∈ [Expr.var 0], arg.ReadsBelow H s.regs s.mem from by
      intro s hs
      simp [Expr.ReadsBelow])
    (show ∀ caller, registerInterface.represents w x caller →
      Contract 1 [doubleFunction] H 0 doubleFunction.body
        (fun s => s = caller.enter ([Expr.var 0].map caller.eval))
        (fun finish => doubleFunction.result.ReadsBelow H finish.regs finish.mem ∧
          registerInterface.represents w (2 * x)
            (caller.leave finish 0 doubleFunction.result)) (fun _ => 4) from by
      intro caller hcaller
      obtain ⟨_, hreg, hin, hout⟩ := hcaller
      apply Source.Verification.verify
      intro entered he
      subst entered
      simp [doubleFunction, Source.Verification.WP.assign_iff, registerInterface,
        Expr.ReadsBelow, LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile,
        Source.State.leave, Source.State.enter, Source.State.setReg, Source.State.eval,
        Expr.eval, BinOp.eval, hreg, hin, hout, BitVec.ofNat_mul, doubleDomain] at hx ⊢
      exact hx)
  simpa [invoke, ABI.callPrefixLocals_length_eq, ABI.returnCodeLocals_length,
    doubleFunction, Expr.compile] using hcall.mono_depth hd

def reader : PolyTimeComponent inputInterface registerInterface (fun x => x) legal where
  toComponent := readerTotal.withTimeBound (fun _ => 1)
    (TotalComponent.TimeBoundOn.of_bound (p := readerTotal)
      (fun _ _ hx => (read_contract hx).timeBound))
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 1
  size_polynomial := Asymptotics.IsPolynomiallyBounded.id

def incrementModule : PolyTimeComponent registerInterface registerInterface
    (fun x => x + 1) incrementDomain where
  toComponent := incrementTotal.withTimeBound (fun _ => 25)
    (TotalComponent.TimeBoundOn.of_bound (p := incrementTotal)
      (fun _ _ hx => (increment_contract hx le_rfl).timeBound))
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 25
  size_polynomial :=
    Asymptotics.IsPolynomiallyBounded.id.add (Asymptotics.IsPolynomiallyBounded.const 1)

def doubleModule : PolyTimeComponent registerInterface registerInterface
    (fun x => 2 * x) doubleDomain where
  toComponent := doubleTotal.withTimeBound (fun _ => 25)
    (TotalComponent.TimeBoundOn.of_bound (p := doubleTotal)
      (fun _ _ hx => (double_contract hx le_rfl).timeBound))
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 25
  size_polynomial :=
    (Asymptotics.IsPolynomiallyBounded.const 2).mul Asymptotics.IsPolynomiallyBounded.id

def writer : PolyTimeComponent registerInterface outputInterface (fun x => x)
    (fun _ _ => True) where
  toComponent := writerTotal.withTimeBound (fun _ => 2)
    (TotalComponent.TimeBoundOn.of_bound (p := writerTotal)
      (fun _ _ _ => write_contract.timeBound))
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 2
  size_polynomial := Asymptotics.IsPolynomiallyBounded.id

/-- Restriction changes only the accepted inputs, not the independently proved
increment program, its function table, or its correctness proof. -/
def incrementStage : PolyTimeComponent registerInterface registerInterface
    (fun x => x + 1) legal where
  toComponent := incrementModule.toComponent.restrict (by
    intro w x hx
    unfold legal at hx
    unfold incrementDomain
    omega)
  time_polynomial := incrementModule.time_polynomial
  size_polynomial := incrementModule.size_polynomial

def arithmetic := doubleModule.comp incrementStage (fun _ _ hx => hx)

/-- The adapters and both function modules run in one persistent source state.
Only the complete executable receives the prologue and final halt. -/
def pipeline := writer.comp (arithmetic.comp reader (fun _ _ hx => hx)) (fun _ _ _ => trivial)

/-- The resource-aware pipeline retains the independently composed functional
program, its domain, all representations and every non-time guarantee. -/
theorem pipeline_toTotalComponent : pipeline.toComponent.toTotalComponent = totalPipeline := rfl

/-- Analyze the linked functional pipeline by adding actual module costs.
This proof is separate from the safe total composition above. -/
theorem totalPipeline_timeBound : totalPipeline.TimeBoundOn (fun _ _ => 53) := by
  have readTime : readerTotal.TimeBoundOn (fun _ _ => 1) :=
    TotalComponent.TimeBoundOn.of_bound (p := readerTotal)
      (fun _ _ hx => (read_contract hx).timeBound)
  have incrementTime : incrementTotal.TimeBoundOn (fun _ _ => 25) :=
    TotalComponent.TimeBoundOn.of_bound (p := incrementTotal)
      (fun _ _ hx => (increment_contract hx le_rfl).timeBound)
  have doubleTime : doubleTotal.TimeBoundOn (fun _ _ => 25) :=
    TotalComponent.TimeBoundOn.of_bound (p := doubleTotal)
      (fun _ _ hx => (double_contract hx le_rfl).timeBound)
  have writeTime : writerTotal.TimeBoundOn (fun _ _ => 2) :=
    TotalComponent.TimeBoundOn.of_bound (p := writerTotal)
      (fun _ _ _ => write_contract.timeBound)
  let incrementStage := incrementTotal.restrict (fun _ _ hx => incrementDomain_of_legal hx)
  have stageTime : incrementStage.TimeBoundOn (fun _ _ => 25) :=
    TotalComponent.TimeBoundOn.restrict (p := incrementTotal) incrementTime
      (fun _ _ hx => incrementDomain_of_legal hx)
  let arithmetic := doubleTotal.comp incrementStage (fun _ _ hx => hx)
  have arithmeticTime : arithmetic.TimeBoundOn (fun _ _ => 50) :=
    TotalComponent.TimeBoundOn.comp (p := incrementStage) (q := doubleTotal)
      doubleTime stageTime (fun _ _ hx => hx)
  let readArithmetic := arithmetic.comp readerTotal (fun _ _ hx => hx)
  have readArithmeticTime : readArithmetic.TimeBoundOn (fun _ _ => 51) :=
    TotalComponent.TimeBoundOn.comp (p := readerTotal) (q := arithmetic)
      arithmeticTime readTime (fun _ _ hx => hx)
  intro w x hx H depth hH hd
  exact TotalComponent.TimeBoundOn.comp (p := readArithmetic) (q := writerTotal)
    writeTime readArithmeticTime (fun _ _ _ => trivial) (w := w) x hx H depth hH hd

/-- Attaching the pipeline bound recovers the existing costed executable. -/
theorem totalPipeline_withTimeBound_code :
    (totalPipeline.withTimeBound (fun _ => 53) totalPipeline_timeBound).code =
      pipeline.toComponent.code := rfl

/-- The independently numbered functions are both present once. -/
theorem pipeline_functions : pipeline.functions = [incrementFunction, doubleFunction] := rfl

/-- The second module's original call to zero has automatically become a call
to one. No edit to `double_contract` was needed. -/
theorem pipeline_body : pipeline.body =
    .seq (.seq (.read 0) (.seq (.call 0 0 [.var 0]) (.call 0 1 [.var 0])))
      (.write (.var 0)) := rfl

theorem pipeline_time (n : Nat) : pipeline.toComponent.totalTime n = 55 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict, Component.totalTime,
    TotalComponent.withTimeBound, readerTotal, incrementTotal, doubleTotal, writerTotal,
    TotalComponent.ofNamed]

theorem pipeline_heap (n : Nat) : pipeline.heapBound n = 0 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict,
    TotalComponent.withTimeBound, readerTotal, incrementTotal, doubleTotal, writerTotal,
    TotalComponent.ofNamed]

theorem pipeline_capacity (n : Nat) : pipeline.toComponent.capacity n = 2 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict, Component.capacity,
    ABI.frameSize, TotalComponent.withTimeBound, readerTotal, incrementTotal, doubleTotal,
    writerTotal, TotalComponent.ofNamed]

theorem pipeline_code_length : pipeline.toComponent.code.length = 55 := rfl

/-- A full halted machine run, with the natural arithmetic answer encoded as
one word. All four modules, the header read, and the halt are in this budget. -/
theorem runs {w x : Nat} (hx : legal w x) (hcode : 55 < 2 ^ w) :
    ∃ finish,
      TerminatesWithin pipeline.toComponent.code 55
        (Ram.State.initial [0, BitVec.ofNat w x]) finish ∧
      finish.output = [BitVec.ofNat w (2 * (x + 1))] ∧ finish.input = [] := by
  have hc : pipeline.toComponent.code.length < 2 ^ w := by
    rw [pipeline_code_length]
    exact hcode
  have hcap : pipeline.toComponent.capacity (inputInterface.size x) < 2 ^ w := by
    rw [pipeline_capacity]
    omega
  obtain ⟨sourceFinal, finish, hrep, ht, _, hout, hin⟩ :=
    pipeline.toComponent.runs x hx [BitVec.ofNat w x] ⟨rfl, rfl⟩ hc hcap
  refine ⟨finish, ?_, hout.trans hrep.2.1, hin.trans hrep.2.2⟩
  simpa only [pipeline_time, pipeline_heap] using ht

/-- This certificate is obtained from `PolyTimeComponent.comp` and its
polynomial closure theorem, not by proving the linked program from scratch. -/
theorem runs_polynomial :
    ∃ c k : Nat, 0 < c ∧ ∀ w x, legal w x → 55 < 2 ^ w →
      ∃ finish,
        TerminatesWithin pipeline.toComponent.code (c * (x + 1) ^ k)
          (Ram.State.initial [0, BitVec.ofNat w x]) finish ∧
        finish.output = [BitVec.ofNat w (2 * (x + 1))] ∧ finish.input = [] := by
  obtain ⟨c, k, hc, run⟩ := pipeline.runs_polynomial
  refine ⟨c, k, hc, ?_⟩
  intro w x hx hcode
  have hcf : pipeline.toComponent.code.length < 2 ^ w := by
    rw [pipeline_code_length]
    exact hcode
  have hcap : pipeline.toComponent.capacity (inputInterface.size x) < 2 ^ w := by
    rw [pipeline_capacity]
    omega
  obtain ⟨sourceFinal, finish, hrep, ht, _, hout, hin⟩ :=
    run w x hx [BitVec.ofNat w x] ⟨rfl, rfl⟩ hcf hcap
  refine ⟨finish, ?_, hout.trans hrep.2.1, hin.trans hrep.2.2⟩
  simpa only [inputInterface, pipeline_heap] using ht

/-- A fixed task specification, independent of any submitted code. Six-bit
or larger words and the mathematical result range determine admissibility;
there is no code-size filter in this definition. -/
def problem : Problem Nat where
  encode w x := [0, BitVec.ofNat w x]
  admissible w x := 6 ≤ w ∧ 2 * (x + 1) < 2 ^ w
  size := fun x => x
  post w x finish :=
    finish.output = [BitVec.ofNat w (2 * (x + 1))] ∧ finish.input = []

private theorem word_capacity {w : Nat} (hw : 6 ≤ w) : 55 < 2 ^ w :=
  Nat.lt_of_lt_of_le (by decide : 55 < 2 ^ 6)
    (Nat.pow_le_pow_right (by decide : 0 < 2) hw)

/-- The certificate covers every legal input of the already fixed problem.
The component export discharges code and stack capacity from the problem's
word-width condition, without shrinking its admissible domain. -/
def certificate : Certificate problem (fun _ => 55) := by
  have exported : Certificate problem pipeline.toComponent.totalTime :=
    pipeline.toComponent.certificate problem (fun w x => [BitVec.ofNat w x]) rfl
      (by intro w x; simp only [problem, pipeline_heap]; rfl)
      (fun _ _ hx => hx.2)
      (fun _ _ _ => ⟨rfl, rfl⟩)
      (by
        intro w x hx
        rw [pipeline_code_length]
        exact word_capacity hx.1)
      (by
        intro w x hx
        rw [pipeline_capacity]
        have hc := word_capacity hx.1
        omega)
      (by
        intro w x hx sourceFinal targetFinal hrep _ hout hin
        exact ⟨hout.trans hrep.2.1, hin.trans hrep.2.2⟩)
  exact exported.weaken (fun n => by rw [pipeline_time])

theorem certificate_code : certificate.code = pipeline.toComponent.code := rfl

/-- Users of the fixed certificate need only establish the published input
conditions; there are no separate submission-dependent fit hypotheses. -/
theorem certificate_runs {w x : Nat} (hx : problem.admissible w x) :
    ∃ finish,
      TerminatesWithin certificate.code 55
        (Ram.State.initial [0, BitVec.ofNat w x]) finish ∧
      finish.output = [BitVec.ofNat w (2 * (x + 1))] ∧ finish.input = [] :=
  certificate.runs hx

end Ram.Examples.Composition
