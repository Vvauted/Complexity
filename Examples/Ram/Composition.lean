/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Component.Composition
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
  locals := 1
  functions := []
  body := .read 0
  valid := by simp [LocalCompiler.Valid, Compiler.Valid, Stmt.WellFormed, Compiler.CallsValid]
  timeBound := fun _ => 1
  heapBound := fun _ => 0
  depthBound := fun _ => 0
  sizeBound := fun x => x
  size_le _ _ _ := Nat.le_refl _
  correct x hx s hs H depth _ _ := read_contract hx s hs
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 1
  size_polynomial := Asymptotics.IsPolynomiallyBounded.id

def incrementModule : PolyTimeComponent registerInterface registerInterface
    (fun x => x + 1) incrementDomain where
  locals := 1
  functions := [incrementFunction]
  body := invoke
  valid := by
    simp [LocalCompiler.Valid, Compiler.Valid, invoke, incrementFunction, Func.WellFormed,
      Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]
  timeBound := fun _ => 25
  heapBound := fun _ => 0
  depthBound := fun _ => 1
  sizeBound := fun x => x + 1
  size_le _ _ _ := Nat.le_refl _
  correct x hx s hs H depth _ hd := increment_contract hx hd s hs
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 25
  size_polynomial := Asymptotics.IsPolynomiallyBounded.id.add (Asymptotics.IsPolynomiallyBounded.const 1)

def doubleModule : PolyTimeComponent registerInterface registerInterface
    (fun x => 2 * x) doubleDomain where
  locals := 1
  functions := [doubleFunction]
  body := invoke
  valid := by
    simp [LocalCompiler.Valid, Compiler.Valid, invoke, doubleFunction, Func.WellFormed,
      Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]
  timeBound := fun _ => 25
  heapBound := fun _ => 0
  depthBound := fun _ => 1
  sizeBound := fun x => 2 * x
  size_le _ _ _ := Nat.le_refl _
  correct x hx s hs H depth _ hd := double_contract hx hd s hs
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 25
  size_polynomial := (Asymptotics.IsPolynomiallyBounded.const 2).mul Asymptotics.IsPolynomiallyBounded.id

def writer : PolyTimeComponent registerInterface outputInterface (fun x => x)
    (fun _ _ => True) where
  locals := 1
  functions := []
  body := .write (.var 0)
  valid := by
    simp [LocalCompiler.Valid, Compiler.Valid, Stmt.WellFormed, Expr.Bounded, Compiler.CallsValid]
  timeBound := fun _ => 2
  heapBound := fun _ => 0
  depthBound := fun _ => 0
  sizeBound := fun x => x
  size_le _ _ _ := Nat.le_refl _
  correct x _ s hs H depth _ _ := write_contract s hs
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

/-- The independently numbered functions are both present once. -/
theorem pipeline_functions : pipeline.functions = [incrementFunction, doubleFunction] := rfl

/-- The second module's original call to zero has automatically become a call
to one. No edit to `double_contract` was needed. -/
theorem pipeline_body : pipeline.body =
    .seq (.seq (.read 0) (.seq (.call 0 0 [.var 0]) (.call 0 1 [.var 0])))
      (.write (.var 0)) := rfl

theorem pipeline_time (n : Nat) : pipeline.toComponent.totalTime n = 55 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict, Component.totalTime]

theorem pipeline_heap (n : Nat) : pipeline.heapBound n = 0 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict]

theorem pipeline_capacity (n : Nat) : pipeline.toComponent.capacity n = 2 := by
  simp [pipeline, arithmetic, incrementStage, incrementModule, doubleModule, reader, writer,
    PolyTimeComponent.comp, Component.comp, Component.restrict, Component.capacity,
    ABI.frameSize]

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
