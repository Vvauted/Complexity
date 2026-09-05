import Ram.ExprCompile

/-!
# Target-level control flow

These rules compose actual `Exec` derivations for branch bodies. Generated
labels are determined by code lengths, and the resulting counts include the
machine transitions that test a condition and traverse a back edge. No source
operation prices or assumptions about an unimplemented compiler are used.
-/

namespace Ram

namespace State

def atPC (s : State w) (pc : Nat) : State w := { s with pc := pc }

@[simp] theorem atPC_pc (s : State w) (pc : Nat) : (s.atPC pc).pc = pc := rfl
@[simp] theorem atPC_regs (s : State w) (pc : Nat) : (s.atPC pc).regs = s.regs := rfl
@[simp] theorem atPC_mem (s : State w) (pc : Nat) : (s.atPC pc).mem = s.mem := rfl
@[simp] theorem atPC_input (s : State w) (pc : Nat) : (s.atPC pc).input = s.input := rfl
@[simp] theorem atPC_outputRev (s : State w) (pc : Nat) :
    (s.atPC pc).outputRev = s.outputRev := rfl
@[simp] theorem atPC_status (s : State w) (pc : Nat) :
    (s.atPC pc).status = s.status := rfl
@[simp] theorem atPC_atPC (s : State w) (a b : Nat) :
    (s.atPC a).atPC b = s.atPC b := rfl
@[simp] theorem atPC_self (s : State w) : s.atPC s.pc = s := rfl

end State

theorem step_jump {code : Code} {s : State w} {target : Nat}
    (hrun : s.status = .running) (hfetch : code[s.pc]? = some (.jump target)) :
    step code s = some (s.atPC target) :=
  step_of_fetch hrun hfetch

theorem step_branchZero_zero {code : Code} {s : State w} {r : Reg} {target : Nat}
    (hrun : s.status = .running)
    (hfetch : code[s.pc]? = some (.branchZero r target)) (hz : s.regs r = 0) :
    step code s = some (s.atPC target) := by
  simpa [execInstr, hz, State.atPC] using step_of_fetch hrun hfetch

theorem step_branchZero_ne_zero {code : Code} {s : State w} {r : Reg} {target : Nat}
    (hrun : s.status = .running)
    (hfetch : code[s.pc]? = some (.branchZero r target)) (hz : s.regs r ≠ 0) :
    step code s = some s.next := by
  simpa only [execInstr, if_neg hz] using step_of_fetch hrun hfetch

namespace Exec

theorem jump {code : Code} {s : State w} {target : Nat}
    (hrun : s.status = .running) (hfetch : code[s.pc]? = some (.jump target)) :
    Exec code 1 s (s.atPC target) := single (step_jump hrun hfetch)

theorem branchZero_zero {code : Code} {s : State w} {r : Reg} {target : Nat}
    (hrun : s.status = .running)
    (hfetch : code[s.pc]? = some (.branchZero r target)) (hz : s.regs r = 0) :
    Exec code 1 s (s.atPC target) := single (step_branchZero_zero hrun hfetch hz)

theorem branchZero_ne_zero {code : Code} {s : State w} {r : Reg} {target : Nat}
    (hrun : s.status = .running)
    (hfetch : code[s.pc]? = some (.branchZero r target)) (hz : s.regs r ≠ 0) :
    Exec code 1 s s.next := single (step_branchZero_ne_zero hrun hfetch hz)

end Exec

/-- The nonzero branch falls through to `yes`; the zero branch jumps to `no`.
The jump after `yes` skips `no`. Both branch programs may contain control flow. -/
def ifCode (cond : Code) (r : Reg) (yes no : Code) (base : Nat) : Code :=
  cond ++ .branchZero r (base + cond.length + yes.length + 2) ::
    (yes ++ .jump (base + cond.length + yes.length + no.length + 2) :: no)

/-- A zero condition exits; a nonzero condition executes the body and jumps
back to the first condition instruction. The body may contain control flow. -/
def whileCode (cond : Code) (r : Reg) (body : Code) (base : Nat) : Code :=
  cond ++ .branchZero r (base + cond.length + body.length + 2) ::
    (body ++ [.jump base])

@[simp] theorem ifCode_length (cond : Code) (r : Reg) (yes no : Code) (base : Nat) :
    (ifCode cond r yes no base).length = cond.length + yes.length + no.length + 2 := by
  simp [ifCode]
  omega

@[simp] theorem whileCode_length (cond : Code) (r : Reg) (body : Code) (base : Nat) :
    (whileCode cond r body base).length = cond.length + body.length + 2 := by
  simp [whileCode]
  omega

/-- The code positions needed to compose either branch inside surrounding code. -/
structure IfLayout (code cond : Code) (r : Reg) (yes no : Code) (base : Nat) : Prop where
  condition : CodeAt code base cond
  test : code[base + cond.length]? =
    some (.branchZero r (base + cond.length + yes.length + 2))
  yesBlock : CodeAt code (base + cond.length + 1) yes
  skip : code[base + cond.length + yes.length + 1]? =
    some (.jump (base + cond.length + yes.length + no.length + 2))
  noBlock : CodeAt code (base + cond.length + yes.length + 2) no

theorem ifCode_layout {code cond yes no : Code} {r : Reg} {base : Nat}
    (h : CodeAt code base (ifCode cond r yes no base)) :
    IfLayout code cond r yes no base := by
  change CodeAt code base (cond ++ _ :: (yes ++ _ :: no)) at h
  have hc := h.append_left
  have ht := h.append_right
  have hy := ht.tail
  have hj := hy.append_right
  refine ⟨hc, ht.head, hy.append_left, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj.head
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj.tail

/-- The condition, body, and actual back-edge instruction in surrounding code. -/
structure WhileLayout (code cond : Code) (r : Reg) (body : Code) (base : Nat) : Prop where
  condition : CodeAt code base cond
  test : code[base + cond.length]? =
    some (.branchZero r (base + cond.length + body.length + 2))
  bodyBlock : CodeAt code (base + cond.length + 1) body
  back : code[base + cond.length + body.length + 1]? = some (.jump base)

theorem whileCode_layout {code cond body : Code} {r : Reg} {base : Nat}
    (h : CodeAt code base (whileCode cond r body base)) :
    WhileLayout code cond r body base := by
  change CodeAt code base (cond ++ _ :: (body ++ [_])) at h
  have hc := h.append_left
  have ht := h.append_right
  have hb := ht.tail
  refine ⟨hc, ht.head, hb.append_left, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb.append_right.head

/-- A zero condition takes the else branch. The caller supplies the actual
execution of that branch, so nested control flow remains compositional. -/
theorem ifCode_else {code cond yes no : Code} {r : Reg} {s u : State w} {n : Nat}
    (hAt : CodeAt code s.pc (ifCode cond r yes no s.pc))
    (hlinear : ∀ i ∈ cond, i.Linear) (hrun : s.status = .running)
    (hz : (execBlock cond s).regs r = 0)
    (hbody : Exec code n
      ((execBlock cond s).atPC (s.pc + cond.length + yes.length + 2)) u) :
    Exec code (cond.length + 1 + n) s u := by
  have hl := ifCode_layout hAt
  have hc := execBlock_exec hl.condition hlinear hrun
  have ht : Exec code 1 (execBlock cond s)
      ((execBlock cond s).atPC (s.pc + cond.length + yes.length + 2)) := by
    apply Exec.branchZero_zero
    · exact (execBlock_status cond s hlinear).trans hrun
    · simpa only [execBlock_pc cond s hlinear] using hl.test
    · exact hz
  exact (hc.trans ht).trans hbody

/-- A nonzero condition takes the then branch and executes the following skip
jump. Its endpoint must be running at that actual jump instruction. -/
theorem ifCode_then {code cond yes no : Code} {r : Reg} {s u : State w} {n : Nat}
    (hAt : CodeAt code s.pc (ifCode cond r yes no s.pc))
    (hlinear : ∀ i ∈ cond, i.Linear) (hrun : s.status = .running)
    (hz : (execBlock cond s).regs r ≠ 0)
    (hbody : Exec code n (execBlock cond s).next u)
    (hpc : u.pc = s.pc + cond.length + yes.length + 1)
    (hurun : u.status = .running) :
    Exec code (cond.length + 1 + n + 1) s
      (u.atPC (s.pc + cond.length + yes.length + no.length + 2)) := by
  have hl := ifCode_layout hAt
  have hc := execBlock_exec hl.condition hlinear hrun
  have ht : Exec code 1 (execBlock cond s) (execBlock cond s).next := by
    apply Exec.branchZero_ne_zero
    · exact (execBlock_status cond s hlinear).trans hrun
    · simpa only [execBlock_pc cond s hlinear] using hl.test
    · exact hz
  have hj : Exec code 1 u
      (u.atPC (s.pc + cond.length + yes.length + no.length + 2)) := by
    apply Exec.jump hurun
    simpa only [hpc] using hl.skip
  exact ((hc.trans ht).trans hbody).trans hj

/-- A false loop guard exits after evaluating the condition and taking one
branch transition; the loop body and back edge are not executed. -/
theorem whileCode_exit {code cond body : Code} {r : Reg} {s : State w}
    (hAt : CodeAt code s.pc (whileCode cond r body s.pc))
    (hlinear : ∀ i ∈ cond, i.Linear) (hrun : s.status = .running)
    (hz : (execBlock cond s).regs r = 0) :
    Exec code (cond.length + 1) s
      ((execBlock cond s).atPC (s.pc + cond.length + body.length + 2)) := by
  have hl := whileCode_layout hAt
  have hc := execBlock_exec hl.condition hlinear hrun
  have ht : Exec code 1 (execBlock cond s)
      ((execBlock cond s).atPC (s.pc + cond.length + body.length + 2)) := by
    apply Exec.branchZero_zero
    · exact (execBlock_status cond s hlinear).trans hrun
    · simpa only [execBlock_pc cond s hlinear] using hl.test
    · exact hz
  exact hc.trans ht

/-- One complete true iteration, including evaluation, branch, body, and the
real jump back to the guard. The supplied body execution may have any length. -/
theorem whileCode_iter {code cond body : Code} {r : Reg} {s u : State w} {n : Nat}
    (hAt : CodeAt code s.pc (whileCode cond r body s.pc))
    (hlinear : ∀ i ∈ cond, i.Linear) (hrun : s.status = .running)
    (hz : (execBlock cond s).regs r ≠ 0)
    (hbody : Exec code n (execBlock cond s).next u)
    (hpc : u.pc = s.pc + cond.length + body.length + 1)
    (hurun : u.status = .running) :
    Exec code (cond.length + 1 + n + 1) s (u.atPC s.pc) := by
  have hl := whileCode_layout hAt
  have hc := execBlock_exec hl.condition hlinear hrun
  have ht : Exec code 1 (execBlock cond s) (execBlock cond s).next := by
    apply Exec.branchZero_ne_zero
    · exact (execBlock_status cond s hlinear).trans hrun
    · simpa only [execBlock_pc cond s hlinear] using hl.test
    · exact hz
  have hj : Exec code 1 u (u.atPC s.pc) := by
    apply Exec.jump hurun
    simpa only [hpc] using hl.back
  exact ((hc.trans ht).trans hbody).trans hj

/-- Compose a true iteration with any proved continuation from the loop head.
This is the induction step for finite loop executions. -/
theorem whileCode_iter_trans {code cond body : Code} {r : Reg}
    {s u t : State w} {n m : Nat}
    (hAt : CodeAt code s.pc (whileCode cond r body s.pc))
    (hlinear : ∀ i ∈ cond, i.Linear) (hrun : s.status = .running)
    (hz : (execBlock cond s).regs r ≠ 0)
    (hbody : Exec code n (execBlock cond s).next u)
    (hpc : u.pc = s.pc + cond.length + body.length + 1)
    (hurun : u.status = .running) (hrest : Exec code m (u.atPC s.pc) t) :
    Exec code (cond.length + 1 + n + 1 + m) s t :=
  (whileCode_iter hAt hlinear hrun hz hbody hpc hurun).trans hrest

namespace Expr

/-- The false-branch rule using the source expression's actual word value. -/
theorem ifCode_else {code yes no : Code} {e : Expr} {r : Reg}
    {s u : State w} {n : Nat} (hb : e.Bounded r)
    (hAt : CodeAt code s.pc (Ram.ifCode (e.compile r) r yes no s.pc))
    (hrun : s.status = .running) (hz : e.eval s.regs s.mem = 0)
    (hbody : Exec code n
      ((execBlock (e.compile r) s).atPC (s.pc + (e.compile r).length + yes.length + 2)) u) :
    Exec code ((e.compile r).length + 1 + n) s u := by
  apply Ram.ifCode_else hAt (compile_linear e r) hrun _ hbody
  rw [(compile_correct hb s).value]
  exact hz

/-- The true-branch rule using the source expression's actual word value. -/
theorem ifCode_then {code yes no : Code} {e : Expr} {r : Reg}
    {s u : State w} {n : Nat} (hb : e.Bounded r)
    (hAt : CodeAt code s.pc (Ram.ifCode (e.compile r) r yes no s.pc))
    (hrun : s.status = .running) (hz : e.eval s.regs s.mem ≠ 0)
    (hbody : Exec code n (execBlock (e.compile r) s).next u)
    (hpc : u.pc = s.pc + (e.compile r).length + yes.length + 1)
    (hurun : u.status = .running) :
    Exec code ((e.compile r).length + 1 + n + 1) s
      (u.atPC (s.pc + (e.compile r).length + yes.length + no.length + 2)) := by
  apply Ram.ifCode_then hAt (compile_linear e r) hrun _ hbody hpc hurun
  rw [(compile_correct hb s).value]
  exact hz

/-- Exit is justified by the compiled expression theorem, not by a separate
condition oracle or a user-assigned guard cost. -/
theorem whileCode_exit {code body : Code} {e : Expr} {r : Reg} {s : State w}
    (hb : e.Bounded r)
    (hAt : CodeAt code s.pc (Ram.whileCode (e.compile r) r body s.pc))
    (hrun : s.status = .running) (hz : e.eval s.regs s.mem = 0) :
    Exec code ((e.compile r).length + 1) s
      ((execBlock (e.compile r) s).atPC (s.pc + (e.compile r).length + body.length + 2)) := by
  apply Ram.whileCode_exit hAt (compile_linear e r) hrun
  rw [(compile_correct hb s).value]
  exact hz

/-- A complete true iteration with a compiled source-expression guard. -/
theorem whileCode_iter {code body : Code} {e : Expr} {r : Reg}
    {s u : State w} {n : Nat} (hb : e.Bounded r)
    (hAt : CodeAt code s.pc (Ram.whileCode (e.compile r) r body s.pc))
    (hrun : s.status = .running) (hz : e.eval s.regs s.mem ≠ 0)
    (hbody : Exec code n (execBlock (e.compile r) s).next u)
    (hpc : u.pc = s.pc + (e.compile r).length + body.length + 1)
    (hurun : u.status = .running) :
    Exec code ((e.compile r).length + 1 + n + 1) s (u.atPC s.pc) := by
  apply Ram.whileCode_iter hAt (compile_linear e r) hrun _ hbody hpc hurun
  rw [(compile_correct hb s).value]
  exact hz

end Expr
end Ram
