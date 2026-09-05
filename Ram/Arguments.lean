import Ram.ABI
import Ram.Memory

/-!
# Verified argument buffering and local-frame initialization

Arguments are evaluated left-to-right in the caller's unchanged source frame.
Each result is moved to a distinct protected argument register. Local-frame
initialization is then a sequence of ordinary moves and zero constants.
The assertions below describe those generated instruction blocks; their
execution counts come exclusively from the existing machine-execution bridge.
-/

namespace Ram.ABI

private theorem control_bounds (n start r : Nat) (hr : r < n + 5) :
    r < 2 * n + 5 ∧ r < n + 5 + start := by
  omega

private theorem outside_tail_bounds (n start len r : Nat)
    (h : r < n + 5 + start ∨ n + 5 + (start + (len + 1)) ≤ r) :
    (r < n + 5 + (start + 1) ∨ n + 5 + (start + 1 + len) ≤ r) ∧
      r ≠ n + 5 + start := by
  omega

/-- The newly filled buffer interval and the frame left untouched around it. -/
structure ArgsEvaluated (n start : Nat) (args : List Expr) (s t : State w) : Prop where
  values : ∀ (i : Nat) (hi : i < args.length),
    t.regs (arg n (start + i)) = args[i].eval s.regs s.mem
  preserved : ∀ r, r < scratch n →
    (r < arg n start ∨ arg n (start + args.length) ≤ r) → t.regs r = s.regs r
  memory : t.mem = s.mem
  input : t.input = s.input
  output : t.outputRev = s.outputRev
  status : t.status = s.status

/-- Argument compilation preserves every local and all five control registers. -/
theorem ArgsEvaluated.control {n start : Nat} {args : List Expr} {s t : State w}
    (h : ArgsEvaluated n start args s t) (r : Reg) (hr : r < n + 5) :
    t.regs r = s.regs r := by
  have hb := control_bounds n start r hr
  exact h.preserved r hb.1 (Or.inl hb.2)

/-- Previously buffered parameters are not overwritten by subsequent ones. -/
theorem ArgsEvaluated.earlier {n start : Nat} {args : List Expr} {s t : State w}
    (h : ArgsEvaluated n start args s t) {i : Nat} (hi : i < start) (hin : i < n) :
    t.regs (arg n i) = s.regs (arg n i) := by
  apply h.preserved
  · change n + 5 + i < 2 * n + 5
    omega
  · left
    change n + 5 + i < n + 5 + start
    omega

/-- Evaluate all arguments in the original caller frame, with no implicit
bulk evaluation or copying operation. -/
theorem evalArgs_correct {n start : Nat} {args : List Expr}
    (hfit : start + args.length ≤ n) (hbounded : ∀ e ∈ args, e.Bounded n)
    (s : State w) : ArgsEvaluated n start args s (execBlock (evalArgs n start args) s) := by
  induction args generalizing start s with
  | nil =>
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro i hi
        simp at hi
      · intro r _ _
        rfl
  | cons e es ih =>
      have hn : n ≤ scratch n := by unfold scratch; omega
      have he : e.Bounded n := hbounded e (by simp)
      have hes : ∀ x ∈ es, x.Bounded n := fun x hx => hbounded x (by simp [hx])
      have hfit' : start + 1 + es.length ≤ n := by
        simp only [List.length_cons] at hfit
        omega
      have hc := Expr.compile_correct (he.mono hn) s
      let u := execInstr (.move (arg n start) (scratch n))
        (execBlock (e.compile (scratch n)) s)
      have huValue : u.regs (arg n start) = e.eval s.regs s.mem := by
        simpa only [u, execInstr, State.next_regs, State.setReg_same] using hc.value
      have huPres : ∀ r, r < scratch n → r ≠ arg n start → u.regs r = s.regs r := by
        intro r hr hne
        simpa only [u, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using
          hc.below r hr
      have huLocal : ∀ r, r < n → u.regs r = s.regs r := by
        intro r hr
        apply huPres r (Nat.lt_of_lt_of_le hr hn)
        change (r : Nat) ≠ n + 5 + start
        omega
      have huMem : u.mem = s.mem := by
        simpa only [u, execInstr, State.next_mem, State.setReg_mem] using hc.memory
      have huInput : u.input = s.input := by
        simpa only [u, execInstr, State.next_input, State.setReg_input] using hc.input
      have huOutput : u.outputRev = s.outputRev := by
        simpa only [u, execInstr, State.next_outputRev, State.setReg_outputRev] using hc.output
      have huStatus : u.status = s.status := by
        simpa only [u, execInstr, State.next_status, State.setReg_status] using hc.status
      have ht := ih hfit' hes u
      simp only [evalArgs, execBlock_append, execBlock_cons, execBlock_nil]
      change ArgsEvaluated n start (e :: es) s (execBlock (evalArgs n (start + 1) es) u)
      refine ⟨?_, ?_, ht.memory.trans huMem, ht.input.trans huInput,
        ht.output.trans huOutput, ht.status.trans huStatus⟩
      · intro i hi
        cases i with
        | zero =>
            have harg : arg n start < scratch n := by
              change n + 5 + start < 2 * n + 5
              omega
            have hp := ht.preserved (arg n start) harg
              (Or.inl (by change n + 5 + start < n + 5 + (start + 1); omega))
            simpa only [Nat.add_zero, List.getElem_cons_zero] using hp.trans huValue
        | succ i =>
            have hi' : i < es.length := by simpa using hi
            have hv := ht.values i hi'
            have hev := Expr.eval_congr (hes es[i] (List.getElem_mem hi')) huLocal huMem
            simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
              hv.trans hev
      · intro r hr hout
        have hb := outside_tail_bounds n start es.length r hout
        exact (ht.preserved r hr hb.1).trans (huPres r hr hb.2)

theorem evalArgs_linear (n start : Nat) (args : List Expr) :
    ∀ i ∈ evalArgs n start args, Instr.Linear i := by
  induction args generalizing start with
  | nil => simp [evalArgs]
  | cons e es ih =>
      intro i hi
      simp only [evalArgs, List.mem_append, List.mem_singleton] at hi
      rcases hi with (he | rfl) | ht
      · exact e.compile_linear (scratch n) i he
      · trivial
      · exact ih (start + 1) i ht

/-- The buffering block executes using exactly its generated instructions. -/
theorem evalArgs_exec {code : Code} {n start : Nat} {args : List Expr} {s : State w}
    (hcode : CodeAt code s.pc (evalArgs n start args)) (hrun : s.status = .running) :
    Exec code (evalArgs n start args).length s (execBlock (evalArgs n start args) s) :=
  execBlock_exec hcode (evalArgs_linear n start args) hrun

/-- Argument buffering preserves a source/target match, including the private
stack/visible-heap separation in `Matches`. -/
theorem ArgsEvaluated.matches {n start heapLimit : Nat} {args : List Expr}
    {source : Source.State w} {s t : State w}
    (h : ArgsEvaluated n start args s t) (hs : source.Matches heapLimit n s) :
    source.Matches heapLimit n t := by
  refine ⟨?_, ?_, hs.input.trans h.input.symm, hs.output.trans h.output.symm,
    h.status.trans hs.running⟩
  · intro r hr
    exact (hs.regs r hr).trans (h.control r (by change (r : Nat) < n + 5; omega)).symm
  · rw [h.memory]
    exact hs.heap

/-- Convert buffered machine values to source values when expression reads
are confined to the source-visible heap. -/
theorem ArgsEvaluated.source_values {n start heapLimit : Nat} {args : List Expr}
    {source : Source.State w} {s t : State w}
    (h : ArgsEvaluated n start args s t) (hs : source.Matches heapLimit n s)
    (hb : ∀ e ∈ args, e.Bounded n)
    (hr : ∀ e ∈ args, e.ReadsBelow heapLimit source.regs source.mem)
    (i : Nat) (hi : i < args.length) :
    t.regs (arg n (start + i)) = source.eval args[i] := by
  exact (h.values i hi).trans
    (hs.eval_eq (hb _ (List.getElem_mem hi)) (hr _ (List.getElem_mem hi))).symm

/-- Effects of copying parameter registers and zeroing the remaining locals. -/
structure LocalsInitialized (n params k : Nat) (s t : State w) : Prop where
  values : ∀ r, r < k → t.regs r = if r < params then s.regs (arg n r) else 0
  preserved : ∀ r, k ≤ r → t.regs r = s.regs r
  memory : t.mem = s.mem
  input : t.input = s.input
  output : t.outputRev = s.outputRev
  status : t.status = s.status

theorem exec_initLocal (n params i : Nat) (s : State w) :
    execInstr (initLocal n params i) s =
      (s.setReg i (if i < params then s.regs (arg n i) else 0)).next := by
  unfold initLocal
  split <;> rfl

/-- Initialization copies each parameter with an ordinary move and initializes
each nonparameter with an ordinary constant instruction. -/
theorem initLocals_correct (n params k : Nat) (s : State w) :
    LocalsInitialized n params k s (execBlock (initLocals n params k) s) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro r hr
        omega
      · intro r _
        rfl
  | succ k ih =>
      simp only [initLocals, execBlock_append, execBlock_cons, execBlock_nil, exec_initLocal]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr
        by_cases he : r = k
        · subst r
          simp only [State.next_regs, State.setReg_same]
          rw [ih.preserved (arg n k) (by unfold arg; omega)]
        · simp only [State.next_regs, State.setReg_ne _ _ _ _ he]
          exact ih.values r (by omega)
      · intro r hr
        simp only [State.next_regs, State.setReg_ne _ _ _ _ (show r ≠ k by omega)]
        exact ih.preserved r (by omega)
      · simpa only [State.next_mem, State.setReg_mem] using ih.memory
      · simpa only [State.next_input, State.setReg_input] using ih.input
      · simpa only [State.next_outputRev, State.setReg_outputRev] using ih.output
      · simpa only [State.next_status, State.setReg_status] using ih.status

theorem initLocal_linear (n params i : Nat) : Instr.Linear (initLocal n params i) := by
  unfold initLocal
  split <;> trivial

theorem initLocals_linear (n params k : Nat) :
    ∀ i ∈ initLocals n params k, Instr.Linear i := by
  induction k with
  | zero => simp [initLocals]
  | succ k ih =>
      intro i hi
      simp only [initLocals, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact ih i hi
      · exact initLocal_linear n params k

/-- The local initialization block executes using its actual emitted code. -/
theorem initLocals_exec {code : Code} {n params k : Nat} {s : State w}
    (hcode : CodeAt code s.pc (initLocals n params k)) (hrun : s.status = .running) :
    Exec code (initLocals n params k).length s (execBlock (initLocals n params k) s) :=
  execBlock_exec hcode (initLocals_linear n params k) hrun

/-- A logical argument list in the buffer yields the same local registers as
the source language's fresh-frame operation, including zeroed nonparameters. -/
theorem initLocals_enter (n : Nat) (source : Source.State w) (s : State w)
    (values : List (Word w))
    (hbuffer : ∀ (i : Nat) (hi : i < values.length), s.regs (arg n i) = values[i])
    (r : Reg) (hr : r < n) :
    (execBlock (initLocals n values.length n) s).regs r = (source.enter values).regs r := by
  rw [(initLocals_correct n values.length n s).values r hr]
  by_cases hi : r < values.length
  · rw [if_pos hi, hbuffer r hi]
    simp [Source.State.enter, List.getElem?_eq_getElem hi]
  · rw [if_neg hi]
    simp [Source.State.enter, List.getElem?_eq_none (Nat.le_of_not_gt hi)]

/-- The complete fresh-local-frame relation, while retaining heap and I/O
agreement and keeping the machine in its running state. -/
theorem initLocals_matches {n heapLimit : Nat} {source : Source.State w} {s : State w}
    (hs : source.Matches heapLimit n s) (values : List (Word w))
    (hbuffer : ∀ (i : Nat) (hi : i < values.length), s.regs (arg n i) = values[i]) :
    (source.enter values).Matches heapLimit n (execBlock (initLocals n values.length n) s) := by
  have hc := initLocals_correct n values.length n s
  refine ⟨?_, ?_, hs.input.trans hc.input.symm, hs.output.trans hc.output.symm,
    hc.status.trans hs.running⟩
  · intro r hr
    exact (initLocals_enter n source s values hbuffer r hr).symm
  · rw [Source.State.enter_mem, hc.memory]
    exact hs.heap

end Ram.ABI
