/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification

/-!
# Total correctness without a time budget

These contracts and weakest preconditions retain terminating execution and
heap/call-depth safety, but do not mention the compiler's register boundary,
instruction counts, or unused fuel. Functional proofs can therefore use
ordinary Lean and mathlib properties before a running-time bound is chosen.

`TotalWP` uses the existing safe source semantics, not a second evaluator.
The erasure lemmas connect existing measured proofs to this interface, and
`TotalContract.compile_heap` still gives an actual halted RAM execution.
Call depth bounds the private stack; it is not a time budget.
-/

namespace Ram.Source

/-- Terminating and safe functional correctness, without a time bound. -/
def TotalContract (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P Q : State w → Prop) : Prop :=
  ∀ s, P s → ∃ t, SafeExec program heapLimit depth stmt s t ∧ Q t

/-- A budget-free total contract whose postcondition retains the entry state. -/
def TotalRelContract (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P : State w → Prop) (Q : State w → State w → Prop) : Prop :=
  ∀ s, P s → ∃ t, SafeExec program heapLimit depth stmt s t ∧ Q s t

namespace TotalContract

variable {w heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P P' Q Q' : State w → Prop}

theorem consequence (h : TotalContract program heapLimit depth stmt P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ t, Q t → Q' t) :
    TotalContract program heapLimit depth stmt P' Q' := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s (pre s hs)
  exact ⟨t, hx, post t hq⟩

theorem mono_post (h : TotalContract program heapLimit depth stmt P Q)
    (post : ∀ t, Q t → Q' t) :
    TotalContract program heapLimit depth stmt P Q' :=
  h.consequence (fun _ hp => hp) post

theorem mono_depth {depth' : Nat}
    (h : TotalContract program heapLimit depth stmt P Q) (hd : depth ≤ depth') :
    TotalContract program heapLimit depth' stmt P Q := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  exact ⟨t, hx.mono hd, hq⟩

theorem totalCorrect (h : TotalContract program heapLimit depth stmt P Q) :
    TotalCorrect program stmt P (fun _ t => Q t) := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  exact ⟨t, hx.erase, hq⟩

theorem skip (P : State w → Prop) :
    TotalContract program heapLimit depth .skip P P := by
  intro s hs
  exact ⟨s, .skip, hs⟩

theorem seq {a b : Stmt} {R : State w → Prop}
    (first : TotalContract program heapLimit depth a P R)
    (second : TotalContract program heapLimit depth b R Q) :
    TotalContract program heapLimit depth (.seq a b) P Q := by
  intro s hs
  obtain ⟨middle, ha, hm⟩ := first s hs
  obtain ⟨t, hb, hq⟩ := second middle hm
  exact ⟨t, .seq ha hb, hq⟩

/-- Retain the actual entry state as a proof-only ghost. -/
theorem with_entry
    (h : ∀ entry, P entry → TotalContract program heapLimit depth stmt
      (fun s => s = entry) Q) :
    TotalContract program heapLimit depth stmt P Q := by
  intro s hs
  exact h s hs s rfl

/-- Functional correctness alone gives a halted compiled execution. Its time
is existential, not a guessed budget. Heap and I/O observations refer to that
same execution; compiler-private stack memory is not exposed. -/
theorem compile_heap {control : Nat} {code : Code} {input : List (Word w)}
    (h : TotalContract program heapLimit depth stmt P Q)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal steps, Q sourceFinal ∧
      Ram.Exec code steps (Ram.State.initial (BitVec.ofNat w heapLimit :: input))
        targetFinal ∧ targetFinal.status = .halted ∧
      HeapEqBelow heapLimit sourceFinal.mem targetFinal.mem ∧
      targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  obtain ⟨sourceFinal, hx, hq⟩ := h (State.initial input) hp
  obtain ⟨steps, measured⟩ := hx.exists_localMeasured control
  obtain ⟨bodyFinish, _, full, halted, heap, output, input⟩ :=
    LocalCompiler.compileChecked_runs_measured_heap hcompile hcodefit hstackfit measured
  exact ⟨sourceFinal, _, steps + 2, hq, full, halted, heap, output, input⟩

end TotalContract

namespace TotalRelContract

variable {w heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P P' : State w → Prop} {Q Q' : State w → State w → Prop}

theorem consequence (h : TotalRelContract program heapLimit depth stmt P Q)
    (pre : ∀ s, P' s → P s) (post : ∀ s t, P' s → Q s t → Q' s t) :
    TotalRelContract program heapLimit depth stmt P' Q' := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s (pre s hs)
  exact ⟨t, hx, post s t hs hq⟩

theorem mono_depth {depth' : Nat}
    (h : TotalRelContract program heapLimit depth stmt P Q) (hd : depth ≤ depth') :
    TotalRelContract program heapLimit depth' stmt P Q := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  exact ⟨t, hx.mono hd, hq⟩

theorem totalCorrect (h : TotalRelContract program heapLimit depth stmt P Q) :
    TotalCorrect program stmt P Q := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  exact ⟨t, hx.erase, hq⟩

theorem toContract {post : State w → Prop}
    (h : TotalRelContract program heapLimit depth stmt P Q)
    (weaken : ∀ entry finish, P entry → Q entry finish → post finish) :
    TotalContract program heapLimit depth stmt P post := by
  intro s hs
  obtain ⟨t, hx, hq⟩ := h s hs
  exact ⟨t, hx, weaken s t hs hq⟩

/-- Compose specifications without unfolding either implementation. The
second specification may retain the original input as a ghost parameter. -/
theorem seq {a b : Stmt} {R : State w → State w → Prop}
    (first : TotalRelContract program heapLimit depth a P R)
    (second : ∀ entry, P entry →
      TotalContract program heapLimit depth b (R entry) (Q entry)) :
    TotalRelContract program heapLimit depth (.seq a b) P Q := by
  intro s hs
  obtain ⟨middle, ha, hm⟩ := first s hs
  obtain ⟨t, hb, hq⟩ := second s hs middle hm
  exact ⟨t, .seq ha hb, hq⟩

end TotalRelContract

theorem Contract.total {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat}
    (h : Contract n program heapLimit depth stmt P Q bound) :
    TotalContract program heapLimit depth stmt P Q := by
  intro s hs
  obtain ⟨_, t, hx, hq, _⟩ := h s hs
  exact ⟨t, hx.erase, hq⟩

theorem RelContract.total {n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop} {bound : State w → Nat}
    (h : RelContract n program heapLimit depth stmt P Q bound) :
    TotalRelContract program heapLimit depth stmt P Q := by
  intro s hs
  obtain ⟨_, t, hx, hq, _⟩ := h s hs
  exact ⟨t, hx.erase, hq⟩

namespace Verification

/-- A total weakest precondition with safety but no time-accounting fields. -/
def TotalWP (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (post : State w → Prop) (s : State w) : Prop :=
  ∃ t, SafeExec program heapLimit depth stmt s t ∧ post t

namespace TotalWP

variable {w heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {post post' : State w → Prop} {s : State w}

theorem mono_post (h : TotalWP program heapLimit depth stmt post s)
    (imp : ∀ t, post t → post' t) : TotalWP program heapLimit depth stmt post' s := by
  obtain ⟨t, hx, hp⟩ := h
  exact ⟨t, hx, imp t hp⟩

theorem mono_depth {depth' : Nat} (h : TotalWP program heapLimit depth stmt post s)
    (hd : depth ≤ depth') : TotalWP program heapLimit depth' stmt post s := by
  obtain ⟨t, hx, hp⟩ := h
  exact ⟨t, hx.mono hd, hp⟩

@[simp] theorem skip_iff : TotalWP program heapLimit depth .skip post s ↔ post s := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx
    exact hp
  · intro hp
    exact ⟨s, .skip, hp⟩

@[simp] theorem assign_iff {dst : Reg} {value : Expr} :
    TotalWP program heapLimit depth (.assign dst value) post s ↔
      value.ReadsBelow heapLimit s.regs s.mem ∧
        post (s.setReg dst (s.eval value)) := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | assign reads => exact ⟨reads, hp⟩
  · rintro ⟨reads, hp⟩
    exact ⟨_, .assign reads, hp⟩

@[simp] theorem store_iff {address value : Expr} :
    TotalWP program heapLimit depth (.store address value) post s ↔
      address.ReadsBelow heapLimit s.regs s.mem ∧
      value.ReadsBelow heapLimit s.regs s.mem ∧
      (s.eval address).toNat < heapLimit ∧
      post (s.setMem (s.eval address) (s.eval value)) := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | store addressReads valueReads destination =>
        exact ⟨addressReads, valueReads, destination, hp⟩
  · rintro ⟨addressReads, valueReads, destination, hp⟩
    exact ⟨_, .store addressReads valueReads destination, hp⟩

@[simp] theorem read_iff {dst : Reg} :
    TotalWP program heapLimit depth (.read dst) post s ↔
      match s.input with
      | [] => False
      | value :: rest => post { s.setReg dst value with input := rest } := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | read available => simpa only [available] using hp
  · intro h
    cases hi : s.input with
    | nil => simp only [hi] at h
    | cons value rest =>
        simp only [hi] at h
        exact ⟨_, .read hi, h⟩

@[simp] theorem write_iff {value : Expr} :
    TotalWP program heapLimit depth (.write value) post s ↔
      value.ReadsBelow heapLimit s.regs s.mem ∧
      post { s with outputRev := s.eval value :: s.outputRev } := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | write reads => exact ⟨reads, hp⟩
  · rintro ⟨reads, hp⟩
    exact ⟨_, .write reads, hp⟩

@[simp] theorem seq_iff {first second : Stmt} :
    TotalWP program heapLimit depth (.seq first second) post s ↔
      TotalWP program heapLimit depth first
        (TotalWP program heapLimit depth second post) s := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | seq first second => exact ⟨_, first, t, second, hp⟩
  · rintro ⟨middle, first, t, second, hp⟩
    exact ⟨t, .seq first second, hp⟩

@[simp] theorem ite_iff {condition : Expr} {yes no : Stmt} :
    TotalWP program heapLimit depth (.ite condition yes no) post s ↔
      condition.ReadsBelow heapLimit s.regs s.mem ∧
      if s.eval condition = 0 then TotalWP program heapLimit depth no post s
      else TotalWP program heapLimit depth yes post s := by
  constructor
  · rintro ⟨t, hx, hp⟩
    cases hx with
    | iteTrue reads condition body =>
        refine ⟨reads, ?_⟩
        rw [if_neg condition]
        exact ⟨t, body, hp⟩
    | iteFalse reads condition body =>
        refine ⟨reads, ?_⟩
        rw [if_pos condition]
        exact ⟨t, body, hp⟩
  · rintro ⟨reads, h⟩
    by_cases hz : s.eval condition = 0
    · rw [if_pos hz] at h
      obtain ⟨t, body, hp⟩ := h
      exact ⟨t, .iteFalse reads hz body, hp⟩
    · rw [if_neg hz] at h
      obtain ⟨t, body, hp⟩ := h
      exact ⟨t, .iteTrue reads hz body, hp⟩

theorem of_contract {P Q : State w → Prop}
    (contract : TotalContract program heapLimit depth stmt P Q) (pre : P s)
    (continuation : ∀ t, Q t → post t) :
    TotalWP program heapLimit depth stmt post s := by
  obtain ⟨t, hx, hq⟩ := contract s pre
  exact ⟨t, hx, continuation t hq⟩

theorem of_relContract {P : State w → Prop} {Q : State w → State w → Prop}
    (contract : TotalRelContract program heapLimit depth stmt P Q) (pre : P s)
    (continuation : ∀ t, Q s t → post t) :
    TotalWP program heapLimit depth stmt post s := by
  obtain ⟨t, hx, hq⟩ := contract s pre
  exact ⟨t, hx, continuation t hq⟩

/-- Apply a function specification without unfolding its body. Only real
argument, return-read and call-depth safety obligations remain. -/
theorem call {f : Func} {fn dst bodyDepth : Nat} {args : List Expr}
    {P : State w → Prop} {Q : State w → State w → Prop}
    (body : TotalRelContract program heapLimit bodyDepth f.body P
      (fun entry finish => f.result.ReadsBelow heapLimit finish.regs finish.mem ∧
        Q entry finish))
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit s.regs s.mem)
    (pre : P (s.enter (args.map s.eval))) (nesting : bodyDepth + 1 ≤ depth)
    (continuation : ∀ callee, Q (s.enter (args.map s.eval)) callee →
      post (s.leave callee dst f.result)) :
    TotalWP program heapLimit depth (.call dst fn args) post s := by
  obtain ⟨callee, execution, reads, result⟩ := body _ pre
  exact ⟨_, (SafeExec.call (dst := dst) lookup arity frame arguments execution reads).mono nesting,
    continuation callee result⟩

/-- A mathematical well-founded relation supplies loop termination. There is
no need to find an instruction budget before proving the invariant and result. -/
theorem while_wellFounded {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) {r : State w → State w → Prop} (wf : WellFounded r)
    (reads : ∀ t, invariant t → condition.ReadsBelow heapLimit t.regs t.mem)
    (iteration : ∀ entry, invariant entry → entry.eval condition ≠ 0 →
      TotalWP program heapLimit depth body (fun t => invariant t ∧ r t entry) entry)
    (pre : invariant s)
    (continuation : ∀ t, invariant t → t.eval condition = 0 → post t) :
    TotalWP program heapLimit depth (.while condition body) post s := by
  have loop : ∀ entry, invariant entry →
      TotalWP program heapLimit depth (.while condition body)
        (fun t => invariant t ∧ t.eval condition = 0) entry := by
    intro entry
    induction entry using wf.induction with
    | h entry ih =>
        intro hinv
        by_cases hz : entry.eval condition = 0
        · exact ⟨entry, .whileFalse (reads entry hinv) hz, hinv, hz⟩
        · obtain ⟨middle, hbody, hmiddle, decrease⟩ := iteration entry hinv hz
          obtain ⟨t, hrest, ht⟩ := ih middle decrease hmiddle
          exact ⟨t, .whileTrue (reads entry hinv) hz hbody hrest, ht⟩
  exact (loop s pre).mono_post (fun t ht => continuation t ht.1 ht.2)

/-- Natural variants are the usual specialization of well-founded descent;
they count progress, not machine instructions. -/
theorem while_variant {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant : State w → Nat)
    (reads : ∀ t, invariant t → condition.ReadsBelow heapLimit t.regs t.mem)
    (iteration : ∀ entry, invariant entry → entry.eval condition ≠ 0 →
      TotalWP program heapLimit depth body
        (fun t => invariant t ∧ variant t < variant entry) entry)
    (pre : invariant s)
    (continuation : ∀ t, invariant t → t.eval condition = 0 → post t) :
    TotalWP program heapLimit depth (.while condition body) post s :=
  while_wellFounded invariant (measure variant).wf reads iteration pre continuation

end TotalWP

theorem WP.total {n heapLimit depth fuel : Nat} {program : Program} {stmt : Stmt}
    {post : State w → Nat → Prop} {s : State w}
    (h : WP n program heapLimit depth stmt post s fuel) :
    TotalWP program heapLimit depth stmt (fun t => ∃ remaining, post t remaining) s := by
  obtain ⟨steps, t, hx, _, hp⟩ := h
  exact ⟨t, hx.erase, fuel - steps, hp⟩

theorem totalContract_iff {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} :
    TotalContract program heapLimit depth stmt P Q ↔
      ∀ s, P s → TotalWP program heapLimit depth stmt Q s := Iff.rfl

theorem verify_total {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop}
    (conditions : ∀ s, P s → TotalWP program heapLimit depth stmt Q s) :
    TotalContract program heapLimit depth stmt P Q := conditions

theorem verify_total_rel {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop}
    (conditions : ∀ s, P s → TotalWP program heapLimit depth stmt (Q s) s) :
    TotalRelContract program heapLimit depth stmt P Q := conditions

end Verification

end Ram.Source
