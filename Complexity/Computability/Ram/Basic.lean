/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Word

/-!
# A deterministic word-RAM

The instruction vocabulary is fixed and does not contain arbitrary Lean
computations. One successful call of `step` is one machine transition; there is
no operation-specific cost function. In particular, memory load/store accesses
one word, and multiplication is the fixed-width multiplication of `Ram.Word`.

Registers and the program counter are named by naturals in the formalization.
A finite program names finitely many registers; the memory address space and
every stored datum are words. Direct code addresses are static program labels.
The register-indirect jump interprets a word as a code address.
-/

namespace Ram

abbrev Reg := Nat

/-- The finite vocabulary of word-RAM instructions. -/
inductive Instr where
  | const (dst : Reg) (value : Nat)
  | move (dst src : Reg)
  | binop (op : BinOp) (dst lhs rhs : Reg)
  | load (dst addrReg : Reg)
  | store (addrReg src : Reg)
  | jump (target : Nat)
  | jumpReg (targetReg : Reg)
  | branchZero (cond : Reg) (target : Nat)
  | read (dst : Reg)
  | write (src : Reg)
  | halt
  deriving DecidableEq, Repr

abbrev Code := List Instr

/-- Faults are distinct from successful termination. -/
inductive Status where
  | running
  | halted
  | fault
  deriving DecidableEq, Repr

structure State (w : Nat) where
  pc : Nat
  regs : Reg → Word w
  mem : Word w → Word w
  input : List (Word w)
  outputRev : List (Word w)
  status : Status

namespace State

/-- The initial state has zeroed registers and memory. Input is already encoded
as a sequence of words; problem-specific encoding is outside this definition. -/
def initial (input : List (Word w)) : State w where
  pc := 0
  regs := fun _ => 0
  mem := fun _ => 0
  input := input
  outputRev := []
  status := .running

def setReg (s : State w) (dst : Reg) (value : Word w) : State w :=
  { s with regs := fun r => if r = dst then value else s.regs r }

def setMem (s : State w) (addr value : Word w) : State w :=
  { s with mem := fun a => if a = addr then value else s.mem a }

def next (s : State w) : State w := { s with pc := s.pc + 1 }

/-- Output in the order it was written. Reversed storage makes each write a
single constructor operation in the executable reference implementation. -/
def output (s : State w) : List (Word w) := s.outputRev.reverse

@[simp] theorem setReg_same (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).regs dst = value := by
  simp [setReg]

@[simp] theorem setReg_ne (s : State w) (dst r : Reg) (value : Word w)
    (h : r ≠ dst) : (s.setReg dst value).regs r = s.regs r := by
  simp [setReg, h]

@[simp] theorem setReg_pc (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).pc = s.pc := rfl

@[simp] theorem setReg_mem (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).mem = s.mem := rfl

@[simp] theorem setReg_input (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).input = s.input := rfl

@[simp] theorem setReg_outputRev (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).outputRev = s.outputRev := rfl

@[simp] theorem setReg_status (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).status = s.status := rfl

@[simp] theorem setMem_same (s : State w) (addr value : Word w) :
    (s.setMem addr value).mem addr = value := by
  simp [setMem]

@[simp] theorem setMem_ne (s : State w) (addr a value : Word w)
    (h : a ≠ addr) : (s.setMem addr value).mem a = s.mem a := by
  simp [setMem, h]

@[simp] theorem setMem_pc (s : State w) (addr value : Word w) :
    (s.setMem addr value).pc = s.pc := rfl

@[simp] theorem setMem_regs (s : State w) (addr value : Word w) :
    (s.setMem addr value).regs = s.regs := rfl

@[simp] theorem setMem_input (s : State w) (addr value : Word w) :
    (s.setMem addr value).input = s.input := rfl

@[simp] theorem setMem_outputRev (s : State w) (addr value : Word w) :
    (s.setMem addr value).outputRev = s.outputRev := rfl

@[simp] theorem setMem_status (s : State w) (addr value : Word w) :
    (s.setMem addr value).status = s.status := rfl

@[simp] theorem next_pc (s : State w) : s.next.pc = s.pc + 1 := rfl
@[simp] theorem next_regs (s : State w) : s.next.regs = s.regs := rfl
@[simp] theorem next_mem (s : State w) : s.next.mem = s.mem := rfl
@[simp] theorem next_input (s : State w) : s.next.input = s.input := rfl
@[simp] theorem next_outputRev (s : State w) : s.next.outputRev = s.outputRev := rfl
@[simp] theorem next_status (s : State w) : s.next.status = s.status := rfl

end State

/-- Execute the body of one instruction. Fetching and the running-state guard
belong to `step`. Reading exhausted input faults; a halt instruction succeeds
and enters the halted state. -/
def execInstr (i : Instr) (s : State w) : State w :=
  match i with
  | .const dst value => (s.setReg dst (BitVec.ofNat w value)).next
  | .move dst src => (s.setReg dst (s.regs src)).next
  | .binop op dst lhs rhs => (s.setReg dst (op.eval (s.regs lhs) (s.regs rhs))).next
  | .load dst addrReg => (s.setReg dst (s.mem (s.regs addrReg))).next
  | .store addrReg src => (s.setMem (s.regs addrReg) (s.regs src)).next
  | .jump target => { s with pc := target }
  | .jumpReg targetReg => { s with pc := (s.regs targetReg).toNat }
  | .branchZero cond target =>
      if s.regs cond = 0 then { s with pc := target } else s.next
  | .read dst =>
      match s.input with
      | [] => { s with status := .fault }
      | value :: rest => { (s.setReg dst value).next with input := rest }
  | .write src => { s.next with outputRev := s.regs src :: s.outputRev }
  | .halt => { s with status := .halted }

/-- Fetch and execute exactly one machine instruction. A stopped state or an
invalid code address has no transition. Every `some` result counts as one step,
including the transition that executes `halt` or encounters an input fault. -/
def step (code : Code) (s : State w) : Option (State w) :=
  if s.status = .running then
    match code[s.pc]? with
    | none => none
    | some i => some (execInstr i s)
  else none

theorem step_of_fetch {code : Code} {s : State w} {i : Instr}
    (hrun : s.status = .running) (hfetch : code[s.pc]? = some i) :
    step code s = some (execInstr i s) := by
  simp [step, hrun, hfetch]

@[simp] theorem step_of_not_running {code : Code} {s : State w}
    (h : s.status ≠ .running) : step code s = none := by
  simp [step, h]

@[simp] theorem step_of_halted {code : Code} {s : State w}
    (h : s.status = .halted) : step code s = none := by
  simp [step, h]

@[simp] theorem step_of_fault {code : Code} {s : State w}
    (h : s.status = .fault) : step code s = none := by
  simp [step, h]

theorem step_of_invalid_pc {code : Code} {s : State w}
    (h : code[s.pc]? = none) : step code s = none := by
  simp [step, h]

theorem step_deterministic {code : Code} {s t u : State w}
    (ht : step code s = some t) (hu : step code s = some u) : t = u := by
  exact Option.some.inj (ht.symm.trans hu)

theorem running_of_step {code : Code} {s t : State w}
    (h : step code s = some t) : s.status = .running := by
  by_cases hr : s.status = .running
  · exact hr
  · simp [step, hr] at h

theorem step_iff {code : Code} {s t : State w} :
    step code s = some t ↔
      s.status = .running ∧ ∃ i, code[s.pc]? = some i ∧ execInstr i s = t := by
  constructor
  · intro h
    have hr := running_of_step h
    refine ⟨hr, ?_⟩
    cases hf : code[s.pc]? with
    | none => simp [step, hr, hf] at h
    | some i =>
        refine ⟨i, rfl, ?_⟩
        simpa [step, hr, hf] using h
  · rintro ⟨hr, i, hi, rfl⟩
    exact step_of_fetch hr hi

@[simp] theorem execInstr_halt_status (s : State w) :
    (execInstr .halt s).status = .halted := rfl

@[simp] theorem execInstr_write_output (s : State w) (src : Reg) :
    (execInstr (.write src) s).output = s.output ++ [s.regs src] := by
  simp [execInstr, State.output]

end Ram
