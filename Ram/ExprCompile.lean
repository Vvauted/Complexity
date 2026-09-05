import Ram.Expr
import Ram.Block

/-!
# Expression compilation and its machine semantics

Source registers lie below `dst`; registers at and above `dst` are scratch.
The compiler evaluates left-to-right and retains a left operand while compiling
the right operand one register higher. The correctness theorem proves this
freshness discipline, the resulting value, and preservation of heap and I/O.
The time theorem counts the resulting RAM transitions, not source annotations.
-/

namespace Ram.Expr

def compile : Expr → Reg → Code
  | .const n, dst => [.const dst n]
  | .var x, dst => [.move dst x]
  | .bin op a b, dst =>
      a.compile dst ++ b.compile (dst + 1) ++ [.binop op dst dst (dst + 1)]
  | .load a, dst => a.compile dst ++ [.load dst dst]

theorem compile_linear (e : Expr) (dst : Reg) :
    ∀ i ∈ e.compile dst, Instr.Linear i := by
  induction e generalizing dst with
  | const n => simp [compile, Instr.Linear]
  | var x => simp [compile, Instr.Linear]
  | bin op a b ia ib =>
      intro i hi
      simp only [compile, List.mem_append, List.mem_singleton] at hi
      rcases hi with (ha | hb) | rfl
      · exact ia dst i ha
      · exact ib (dst + 1) i hb
      · trivial
  | load a ih =>
      intro i hi
      simp only [compile, List.mem_append, List.mem_singleton] at hi
      rcases hi with ha | rfl
      · exact ih dst i ha
      · trivial

/-- The output and the source-visible part of the frame. Scratch registers are
deliberately not equated to the input state. -/
structure Compiled (e : Expr) (dst : Reg) (s t : State w) : Prop where
  value : t.regs dst = e.eval s.regs s.mem
  below : ∀ x, x < dst → t.regs x = s.regs x
  memory : t.mem = s.mem
  input : t.input = s.input
  output : t.outputRev = s.outputRev
  status : t.status = s.status

/-- Every compiled expression computes its specified word, while preserving
all source variables and all memory and I/O effects. -/
theorem compile_correct {e : Expr} {dst : Reg} (hb : e.Bounded dst) (s : State w) :
    Compiled e dst s (execBlock (e.compile dst) s) := by
  induction e generalizing dst s with
  | const n =>
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp [compile, execBlock, execInstr, eval, State.setReg, State.next]
      · intro x hx
        simp [compile, execBlock, execInstr, State.setReg, State.next,
          Nat.ne_of_lt hx]
  | var v =>
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · simp [compile, execBlock, execInstr, eval, State.setReg, State.next]
      · intro x hx
        simp [compile, execBlock, execInstr, State.setReg, State.next,
          Nat.ne_of_lt hx]
  | bin op a b ia ib =>
      have ha := ia hb.1 s
      have hb' := ib (hb.2.mono (Nat.le_succ dst)) (execBlock (a.compile dst) s)
      simp only [compile, execBlock_append, execBlock_cons, execBlock_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [execInstr, State.next_regs, State.setReg_same]
        rw [hb'.below dst (Nat.lt_succ_self dst), ha.value, hb'.value]
        rw [eval_congr hb.2 ha.below ha.memory]
        rfl
      · intro x hx
        simp only [execInstr, State.next_regs,
          State.setReg_ne _ _ _ _ (Nat.ne_of_lt hx)]
        exact (hb'.below x (Nat.lt_trans hx (Nat.lt_succ_self dst))).trans (ha.below x hx)
      · simpa only [execInstr, State.next_mem, State.setReg_mem] using
          hb'.memory.trans ha.memory
      · simpa only [execInstr, State.next_input, State.setReg_input] using
          hb'.input.trans ha.input
      · simpa only [execInstr, State.next_outputRev, State.setReg_outputRev] using
          hb'.output.trans ha.output
      · simpa only [execInstr, State.next_status, State.setReg_status] using
          hb'.status.trans ha.status
  | load a ih =>
      have ha := ih hb s
      simp only [compile, execBlock_append, execBlock_cons, execBlock_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [execInstr, State.next_regs, State.setReg_same, ha.memory, ha.value]
        rfl
      · intro x hx
        simp only [execInstr, State.next_regs,
          State.setReg_ne _ _ _ _ (Nat.ne_of_lt hx)]
        exact ha.below x hx
      · simpa only [execInstr, State.next_mem, State.setReg_mem] using ha.memory
      · simpa only [execInstr, State.next_input, State.setReg_input] using ha.input
      · simpa only [execInstr, State.next_outputRev, State.setReg_outputRev] using ha.output
      · simpa only [execInstr, State.next_status, State.setReg_status] using ha.status

/-- This is an actual execution inside any surrounding machine program. Its
exact count is the generated block length, independent of the surrounding code. -/
theorem compile_exec {code : Code} {e : Expr} {dst : Reg} {s : State w}
    (hcode : CodeAt code s.pc (e.compile dst)) (hrun : s.status = .running) :
    Exec code (e.compile dst).length s (execBlock (e.compile dst) s) :=
  execBlock_exec hcode (compile_linear e dst) hrun

/-- Combine semantic preservation with counted machine execution. -/
theorem compile_refines {code : Code} {e : Expr} {dst : Reg} {s : State w}
    (hb : e.Bounded dst) (hcode : CodeAt code s.pc (e.compile dst))
    (hrun : s.status = .running) :
    ∃ t, Exec code (e.compile dst).length s t ∧ Compiled e dst s t ∧
      t.pc = s.pc + (e.compile dst).length := by
  exact ⟨_, compile_exec hcode hrun, compile_correct hb s,
    execBlock_pc _ s (compile_linear e dst)⟩

/-- A source multiplication, after compilation and execution, has the actual
word-RAM modular result. This follows through the compiler, not a tick table. -/
theorem compiled_mul_toNat {a b : Expr} {dst : Reg} (s : State w)
    (ha : a.Bounded dst) (hb : b.Bounded dst) :
    ((execBlock ((Expr.bin .mul a b).compile dst) s).regs dst).toNat =
      ((a.eval s.regs s.mem).toNat * (b.eval s.regs s.mem).toNat) % 2 ^ w := by
  rw [(compile_correct (e := .bin .mul a b) ⟨ha, hb⟩ s).value]
  exact BinOp.eval_mul_toNat _ _

theorem compiled_mul_toNat_of_lt {a b : Expr} {dst : Reg} (s : State w)
    (ha : a.Bounded dst) (hb : b.Bounded dst)
    (hfit : (a.eval s.regs s.mem).toNat * (b.eval s.regs s.mem).toNat < 2 ^ w) :
    ((execBlock ((Expr.bin .mul a b).compile dst) s).regs dst).toNat =
      (a.eval s.regs s.mem).toNat * (b.eval s.regs s.mem).toNat := by
  rw [compiled_mul_toNat s ha hb, Nat.mod_eq_of_lt hfit]

end Ram.Expr
