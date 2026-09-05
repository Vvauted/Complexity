import Ram.Syntax
import Ram.Measured
import Ram.CodeLength
import Ram.Complexity

/-!
# Ordinary recursive factorial, with exact whole-program machine time

The source and linked code below are fixed, independently of the input and word
width. Each recursive invocation saves and restores the caller through the
ordinary ABI. `factorialNat` is only the mathematical specification: it never
appears in a runtime expression or instruction.

The result is factorial modulo the word range; intermediate multiplication is
allowed to wrap. Only the input, return addresses, and live stack must fit.
-/

namespace Ram.Examples.Factorial

def self : Nat := 0

/-- Register names are allocated by the surface language, not by the user. -/
def factorial : Func := ram_fun% (n) locals (answer) {
  if n {
    answer := call self(n - 1);
    answer := n * answer;
  } else {
    answer := 1;
  }
  return answer;
}

def program : Program := [factorial]

def main : Stmt :=
  let n : Reg := 0
  let answer : Reg := 1
  ram% {
    read n;
    answer := call self(n);
    write answer;
  }

theorem factorial_expands : factorial =
    { params := 1, locals := 2
      body := .ite (.var 0)
        (.seq (.call 1 self [.bin .sub (.var 0) (.const 1)])
          (.assign 1 (.bin .mul (.var 0) (.var 1))))
        (.assign 1 (.const 1))
      result := .var 1 } := rfl

/-- A pure logical specification, not an operation available to the machine. -/
def factorialNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorialNat k

def value (w k : Nat) : Word w := BitVec.ofNat w (factorialNat k)

theorem value_toNat (w k : Nat) :
    (value w k).toNat = factorialNat k % 2 ^ w := BitVec.toNat_ofNat _ _

theorem value_succ (w k : Nat) :
    value w (k + 1) = BitVec.ofNat w (k + 1) * value w k := by
  simp only [value, factorialNat, BitVec.ofNat_mul]

private theorem set_answer_twice (s : Source.State w) (a b : Word w) :
    (s.setReg 1 a).setReg 1 b = s.setReg 1 b := by
  simp only [Source.State.setReg, Source.State.mk.injEq, and_true]
  funext r
  by_cases hr : r = 1 <;> simp [hr]

/-- The callee's local registers are genuinely discarded on return. In
particular, the caller's original `n` survives its recursive call. -/
theorem leave_answer (s : Source.State w) (args : List (Word w)) (answer : Word w) :
    s.leave ((s.enter args).setReg 1 answer) 1 (.var 1) = s.setReg 1 answer := by
  simp [Source.State.leave, Source.State.enter, Source.State.setReg,
    Source.State.eval, Expr.eval]

private theorem encoded_pred (w k : Nat) :
    BitVec.ofNat w (k + 1) - BitVec.ofNat w 1 = BitVec.ofNat w k := by
  rw [BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

/-- Length calculation on the actual generated setup and return instruction
lists. This includes all individual saves, restores, and jumps. -/
theorem recursive_call_steps (bodySteps : Nat) :
    (ABI.callPrefix 2 [.bin .sub (.var 0) (.const 1)] 0).length + 1 + bodySteps +
      (ABI.returnCode 2 (.var 1)).length + 1 = bodySteps + 30 := by
  change 16 + 1 + bodySteps + 12 + 1 = bodySteps + 30
  omega

theorem initial_call_steps (bodySteps : Nat) :
    (ABI.callPrefix 2 [.var 0] 0).length + 1 + bodySteps +
      (ABI.returnCode 2 (.var 1)).length + 1 = bodySteps + 28 := by
  change 14 + 1 + bodySteps + 12 + 1 = bodySteps + 28
  omega

/-- Every input in range terminates. The exact endpoint preserves the entire
caller state except its answer register, not just the final numeric result. -/
theorem body_measured (H k : Nat) (s : Source.State w)
    (hk : k < 2 ^ w) (hn : s.regs 0 = BitVec.ofNat w k) :
    Source.MeasuredExec 2 program H k factorial.body (37 * k + 4)
      s (s.setReg 1 (value w k)) := by
  induction k generalizing s with
  | zero =>
      have hzero : s.eval (.var 0) = 0 := hn
      exact .iteFalse (c := .var 0) trivial hzero
        (.assign (value := .const 1) trivial)
  | succ k ih =>
      have hpred : s.eval (.bin .sub (.var 0) (.const 1)) = BitVec.ofNat w k := by
        change s.regs 0 - BitVec.ofNat w 1 = BitVec.ofNat w k
        rw [hn, encoded_pred]
      have hcallee := ih (s.enter [BitVec.ofNat w k]) (by omega) (by
        simp [Source.State.enter])
      have harguments :
          ∀ arg ∈ [Expr.bin .sub (.var 0) (.const 1)],
            arg.ReadsBelow H s.regs s.mem := by
        simp [Expr.ReadsBelow]
      have hbody : Source.MeasuredExec 2 program H k factorial.body (37 * k + 4)
          (s.enter ([.bin .sub (.var 0) (.const 1)].map s.eval))
          ((s.enter [BitVec.ofNat w k]).setReg 1 (value w k)) := by
        simpa only [List.map_cons, List.map_nil, hpred] using hcallee
      have hcall := Source.MeasuredExec.call (dst := 1) (fn := self)
        (show program[self]? = some factorial from rfl) rfl (by decide)
        harguments hbody (show factorial.result.ReadsBelow H _ _ from trivial)
      have hcall' : Source.MeasuredExec 2 program H (k + 1)
          (.call 1 self [.bin .sub (.var 0) (.const 1)]) (37 * k + 34)
          s (s.setReg 1 (value w k)) := by
        simp only [show factorial.result = .var 1 from rfl,
          recursive_call_steps, leave_answer] at hcall
        simpa only [Nat.add_assoc] using hcall
      have hmul : (s.setReg 1 (value w k)).eval (.bin .mul (.var 0) (.var 1)) =
          value w (k + 1) := by
        simp only [Source.State.eval, Expr.eval, BinOp.eval_mul,
          Source.State.setReg_ne _ _ _ _ (by decide : (0 : Reg) ≠ 1),
          Source.State.setReg_same, hn, value_succ]
      have hassign : Source.MeasuredExec 2 program H (k + 1)
          (.assign 1 (.bin .mul (.var 0) (.var 1))) 4
          (s.setReg 1 (value w k)) (s.setReg 1 (value w (k + 1))) := by
        have h := Source.MeasuredExec.assign (n := 2) (program := program)
          (heapLimit := H) (d := k + 1) (s := s.setReg 1 (value w k))
          (dst := 1) (value := .bin .mul (.var 0) (.var 1)) ⟨trivial, trivial⟩
        simpa only [hmul, set_answer_twice,
          show Compiler.stmtSize 2 (.assign 1 (.bin .mul (.var 0) (.var 1))) = 4
            from rfl] using h
      have hnonzero : s.eval (.var 0) ≠ 0 := by
        change s.regs 0 ≠ 0
        intro hz
        have hnat := congrArg BitVec.toNat hz
        rw [hn, Word.ofNat_toNat_of_lt hk] at hnat
        change k + 1 = 0 at hnat
        omega
      have h := Source.MeasuredExec.iteTrue (c := .var 0) (no := .assign 1 (.const 1))
        trivial hnonzero (.seq hcall' hassign)
      have hcount : 1 + 1 + (37 * k + 34 + 4) + 1 = 37 * (k + 1) + 4 := by omega
      simpa only [show (Expr.compile (.var 0) (ABI.scratch 2)).length = 1 from rfl,
        hcount] using h

/-- The public call restores every caller local other than its destination. -/
theorem call_measured (H k : Nat) (s : Source.State w)
    (hk : k < 2 ^ w) (hn : s.regs 0 = BitVec.ofNat w k) :
    Source.MeasuredExec 2 program H (k + 1) (.call 1 self [.var 0])
      (37 * k + 32) s (s.setReg 1 (value w k)) := by
  have hbody := body_measured H k (s.enter ([.var 0].map s.eval)) hk (by
    simpa [Source.State.enter, Source.State.eval, Expr.eval] using hn)
  have hcall := Source.MeasuredExec.call (dst := 1) (fn := self)
    (show program[self]? = some factorial from rfl) rfl (by decide)
    (show ∀ arg ∈ [Expr.var 0], arg.ReadsBelow H s.regs s.mem from by
      simp [Expr.ReadsBelow]) hbody
    (show factorial.result.ReadsBelow H _ _ from trivial)
  simp only [show factorial.result = .var 1 from rfl,
    initial_call_steps, leave_answer] at hcall
  simpa only [Nat.add_assoc] using hcall

def afterRead (w k : Nat) : Source.State w :=
  { (Source.State.initial [BitVec.ofNat w k]).setReg 0 (BitVec.ofNat w k)
    with input := [] }

def sourceFinal (w k : Nat) : Source.State w :=
  { (afterRead w k).setReg 1 (value w k) with outputRev := [value w k] }

/-- The complete source program consumes one input and emits one result. -/
theorem main_measured (H k : Nat) (hk : k < 2 ^ w) :
    Source.MeasuredExec 2 program H (k + 1) main (37 * k + 35)
      (Source.State.initial [BitVec.ofNat w k]) (sourceFinal w k) := by
  have hread : Source.MeasuredExec 2 program H (k + 1) (.read 0) 1
      (Source.State.initial [BitVec.ofNat w k]) (afterRead w k) := .read rfl
  have hcall := call_measured H k (afterRead w k) hk (by
    simp [afterRead, Source.State.setReg])
  have hwrite : Source.MeasuredExec 2 program H (k + 1) (.write (.var 1)) 2
      ((afterRead w k).setReg 1 (value w k)) (sourceFinal w k) := by
    simpa only [Source.State.eval, Expr.eval, Source.State.setReg_same] using
      (Source.MeasuredExec.write (n := 2) (program := program) (heapLimit := H)
        (d := k + 1) (s := (afterRead w k).setReg 1 (value w k))
        (value := .var 1) trivial)
  have hcount : 1 + (37 * k + 32 + 2) = 37 * k + 35 := by omega
  simpa only [hcount] using Source.MeasuredExec.seq hread (.seq hcall hwrite)

theorem valid : Compiler.Valid 2 program main := by decide

/-- One fixed finite instruction list is used for every runtime input. -/
def code : Code := Compiler.rawLink 2 program main

theorem compile_checked : Compiler.compileChecked 2 program main = some code :=
  Compiler.compileChecked_some_iff.mpr ⟨valid, rfl⟩

/-- The code contains one recursive function body, not `k` unrolled copies. -/
theorem code_length : code.length = 60 := rfl

/-- Exact whole-program execution, including argument evaluation, individual
frame saves/restores, return jumps, the stack-header read, and the final halt.
The input starts with the ABI stack header `H`, followed by the user's `k`.
There are no heap reads in this program, so any nonnegative boundary works. -/
theorem runs (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧ finish.output = [value w k] ∧ finish.input = [] := by
  have hfit : code.length < 2 ^ w := by simpa only [code_length] using hcodefit
  obtain ⟨bodyFinish, _, hfull, hhalt, hout, hin⟩ :=
    Compiler.compileChecked_runs_measured compile_checked hfit hstackfit (main_measured H k hk)
  refine ⟨_, ?_, hhalt, hout, hin⟩
  simpa only [Nat.add_assoc] using hfull

/-- The emitted word decodes to exactly factorial modulo `2^w`, for every
legal input, including inputs whose factorial does not fit in one word. -/
theorem runs_mod_factorial (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧
      finish.output.map BitVec.toNat = [factorialNat k % 2 ^ w] ∧ finish.input = [] := by
  obtain ⟨finish, hx, halt, hout, hin⟩ := runs H k hk hcodefit hstackfit
  exact ⟨finish, hx, halt, by rw [hout]; simp [value_toNat], hin⟩

/-- If the mathematical factorial fits as well, the same execution returns
that exact natural number, without a modular reduction in its specification. -/
theorem runs_factorial_of_lt (H k : Nat) (hk : k < 2 ^ w)
    (hcodefit : 60 < 2 ^ w) (hstackfit : H + (k + 1) * 3 < 2 ^ w)
    (hresult : factorialNat k < 2 ^ w) :
    ∃ finish, Ram.Exec code (37 * k + 37)
        (Ram.State.initial [BitVec.ofNat w H, BitVec.ofNat w k]) finish ∧
      finish.status = .halted ∧
      finish.output.map BitVec.toNat = [factorialNat k] ∧ finish.input = [] := by
  obtain ⟨finish, hx, halt, hout, hin⟩ := runs_mod_factorial H k hk hcodefit hstackfit
  exact ⟨finish, hx, halt, by simpa only [Nat.mod_eq_of_lt hresult] using hout, hin⟩

/-- External input representation: an empty-heap stack header, then the input
number as one unsigned word. Encoding is not an extra machine instruction. -/
def encode (w k : Nat) : List (Word w) := [BitVec.ofNat w 0, BitVec.ofNat w k]

/-- Space for the fixed code and all simultaneously live recursive frames.
This also ensures that the input number itself has an exact word encoding. -/
def admissible (w k : Nat) : Prop := 60 < 2 ^ w ∧ (k + 1) * 3 < 2 ^ w

def post (w k : Nat) (finish : Ram.State w) : Prop :=
  finish.output = [value w k] ∧ finish.input = []

/-- A uniform bound for the same code at every admissible input and width,
with the ordinary terminating RAM execution judgment as its meaning. -/
theorem uniform_time :
    UniformTimeBound code encode admissible id post (fun k => 37 * k + 37) := by
  intro w k hadmissible
  have hk : k < 2 ^ w := by
    have hspace := hadmissible.2
    omega
  obtain ⟨finish, hx, halt, hout, hin⟩ :=
    runs 0 k hk hadmissible.1 (by simpa using hadmissible.2)
  exact ⟨finish, ⟨37 * k + 37, Nat.le_refl _, hx, halt⟩, hout, hin⟩

/-- Linear time in the *numeric value* `k`, uniformly over admissible widths.
This is not linear time in the binary encoding length of `k` (nor in the
number of input words, which is constant for this particular interface). -/
theorem uniform_linear : UniformBigO code encode admissible id post id :=
  uniform_time.linear

end Ram.Examples.Factorial
