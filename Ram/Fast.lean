import Ram.Runner
import Std.Data.TreeMap.Lemmas
import Init.Data.Array.Lemmas

/-!
# Executable array/tree-map representation of the same RAM

Instruction fetch and register lookup use arrays. Sparse memory uses a balanced
`Std.TreeMap` keyed by decoded word addresses. Updates do not accumulate the
reference machine's nested lookup functions. Registers grow only when a write
uses a previously unallocated index; callers may preallocate their fixed
program's register bound when constructing the initial state.

The representation is not a different cost model. `State.toState` observes it
as the existing RAM state, and the instruction/step theorems below prove exact
correspondence. Host array growth, tree balancing, and interpreter wall time
are not additional abstract RAM transitions or performance measurements.
-/

namespace Ram.Fast

/-- Register storage needed by one instruction's explicitly named operands. -/
def instrRegisterCapacity : Instr → Nat
  | .const dst _ => dst + 1
  | .move dst src => max dst src + 1
  | .binop _ dst lhs rhs => max dst (max lhs rhs) + 1
  | .load dst addrReg => max dst addrReg + 1
  | .store addrReg src => max addrReg src + 1
  | .jumpReg targetReg => targetReg + 1
  | .branchZero cond _ => cond + 1
  | .read dst => dst + 1
  | .write src => src + 1
  | .jump _ | .halt => 0

/-- A single scan supplies an optional preallocation size. This does not limit
the semantics: out-of-capacity writes are still handled by `setGrow`. -/
def registerCapacity (code : Array Instr) : Nat :=
  code.foldl (fun capacity i => max capacity (instrRegisterCapacity i)) 0

/-- Total array update with zero-filled extension, preserving the reference
machine's unbounded register-name semantics rather than dropping writes. -/
def setGrow (xs : Array (Word w)) (i : Nat) (value : Word w) : Array (Word w) :=
  if h : i < xs.size then xs.set i value h
  else (xs ++ Array.replicate (i - xs.size) 0).push value

@[simp] theorem getD_replicate_zero (n r : Nat) :
    ((Array.replicate n (0 : Word w))[r]?).getD 0 = 0 := by
  rw [Array.getElem?_replicate]
  split <;> rfl

private theorem getD_append_zeros (xs : Array (Word w)) (n r : Nat) :
    ((xs ++ Array.replicate n 0)[r]?).getD 0 = (xs[r]?).getD 0 := by
  by_cases hr : r < xs.size
  · rw [Array.getElem?_append_left hr]
  · rw [Array.getElem?_append_right (Nat.le_of_not_gt hr),
        Array.getElem?_eq_none (xs := xs) (Nat.le_of_not_gt hr)]
    exact getD_replicate_zero n (r - xs.size)

@[simp] theorem getD_setGrow (xs : Array (Word w)) (i : Nat)
    (value : Word w) (r : Nat) :
    ((setGrow xs i value)[r]?).getD 0 =
      if r = i then value else (xs[r]?).getD 0 := by
  by_cases h : i < xs.size
  · simp only [setGrow, dif_pos h]
    rw [Array.getElem?_set h]
    by_cases hr : r = i
    · subst r
      simp
    · simp [hr, Ne.symm hr]
  · have hs :
        (xs ++ Array.replicate (i - xs.size) (0 : Word w)).size = i := by
      rw [Array.size_append, Array.size_replicate]
      exact Nat.add_sub_of_le (Nat.le_of_not_gt h)
    simp only [setGrow, dif_neg h]
    rw [Array.getElem?_push, hs]
    by_cases hr : r = i
    · simp [hr]
    · simp only [hr, if_false]
      exact getD_append_zeros xs (i - xs.size) r

structure State (w : Nat) where
  pc : Nat
  regs : Array (Word w)
  mem : Std.TreeMap Nat (Word w)
  input : List (Word w)
  outputRev : List (Word w)
  status : Ram.Status

namespace State

@[inline] def getReg (s : State w) (r : Reg) : Word w := s.regs[r]?.getD 0

@[inline] def getMem (s : State w) (a : Word w) : Word w := s.mem.getD a.toNat 0

def toState (s : State w) : Ram.State w where
  pc := s.pc
  regs := s.getReg
  mem := s.getMem
  input := s.input
  outputRev := s.outputRev
  status := s.status

def initial (input : List (Word w)) (registerCapacity : Nat := 0) : State w where
  pc := 0
  regs := Array.replicate registerCapacity 0
  mem := ∅
  input := input
  outputRev := []
  status := .running

@[inline] def setReg (s : State w) (r : Reg) (value : Word w) : State w :=
  { s with regs := setGrow s.regs r value }

@[inline] def setMem (s : State w) (a value : Word w) : State w :=
  { s with mem := s.mem.insert a.toNat value }

@[inline] def next (s : State w) : State w := { s with pc := s.pc + 1 }

def output (s : State w) : List (Word w) := s.outputRev.reverse

@[simp] theorem toState_pc (s : State w) : s.toState.pc = s.pc := rfl
@[simp] theorem toState_regs (s : State w) : s.toState.regs = s.getReg := rfl
@[simp] theorem toState_mem (s : State w) : s.toState.mem = s.getMem := rfl
@[simp] theorem toState_input (s : State w) : s.toState.input = s.input := rfl
@[simp] theorem toState_outputRev (s : State w) : s.toState.outputRev = s.outputRev := rfl
@[simp] theorem toState_status (s : State w) : s.toState.status = s.status := rfl
@[simp] theorem toState_output (s : State w) : s.toState.output = s.output := rfl

@[simp] theorem toState_next (s : State w) : s.next.toState = s.toState.next := rfl

@[simp] theorem toState_with_pc (s : State w) (pc : Nat) :
    ({ s with pc := pc } : State w).toState = { s.toState with pc := pc } := rfl

@[simp] theorem toState_with_input (s : State w) (input : List (Word w)) :
    ({ s with input := input } : State w).toState = { s.toState with input := input } := rfl

@[simp] theorem toState_with_outputRev (s : State w) (outputRev : List (Word w)) :
    ({ s with outputRev := outputRev } : State w).toState =
      { s.toState with outputRev := outputRev } := rfl

@[simp] theorem toState_with_status (s : State w) (status : Status) :
    ({ s with status := status } : State w).toState = { s.toState with status := status } := rfl

@[simp] theorem getReg_setReg (s : State w) (r : Reg) (value : Word w) (query : Reg) :
    (s.setReg r value).getReg query = if query = r then value else s.getReg query := by
  exact getD_setGrow s.regs r value query

@[simp] theorem toState_setReg (s : State w) (r : Reg) (value : Word w) :
    (s.setReg r value).toState = s.toState.setReg r value := by
  simp only [toState, setReg, Ram.State.setReg, Ram.State.mk.injEq,
    true_and, and_true]
  constructor
  · funext query
    exact getReg_setReg s r value query
  · rfl

@[simp] theorem getMem_setMem (s : State w) (a value query : Word w) :
    (s.setMem a value).getMem query = if query = a then value else s.getMem query := by
  change (s.mem.insert a.toNat value).getD query.toNat 0 =
    if query = a then value else s.mem.getD query.toNat 0
  simp only [Std.TreeMap.getD_insert, Std.compare_eq_iff_eq, BitVec.toNat_inj]
  by_cases h : query = a
  · simp [h]
  · simp [h, Ne.symm h]

@[simp] theorem toState_setMem (s : State w) (a value : Word w) :
    (s.setMem a value).toState = s.toState.setMem a value := by
  simp only [toState, setMem, Ram.State.setMem, Ram.State.mk.injEq,
    true_and, and_true]
  constructor
  · rfl
  · funext query
    exact getMem_setMem s a value query

@[simp] theorem toState_initial (input : List (Word w)) (registerCapacity : Nat) :
    (initial input registerCapacity).toState = Ram.State.initial input := by
  simp only [toState, initial, Ram.State.initial, Ram.State.mk.injEq,
    true_and, and_true]
  constructor
  · funext r
    exact getD_replicate_zero registerCapacity r
  · funext a
    exact Std.TreeMap.getD_emptyc

end State

/-- The same fixed instruction vocabulary, using the executable storage
representation. Every branch corresponds to `Ram.execInstr`. -/
def execInstr (i : Instr) (s : State w) : State w :=
  match i with
  | .const dst value => (s.setReg dst (BitVec.ofNat w value)).next
  | .move dst src => (s.setReg dst (s.getReg src)).next
  | .binop op dst lhs rhs => (s.setReg dst (op.eval (s.getReg lhs) (s.getReg rhs))).next
  | .load dst addrReg => (s.setReg dst (s.getMem (s.getReg addrReg))).next
  | .store addrReg src => (s.setMem (s.getReg addrReg) (s.getReg src)).next
  | .jump target => { s with pc := target }
  | .jumpReg targetReg => { s with pc := (s.getReg targetReg).toNat }
  | .branchZero cond target =>
      if s.getReg cond = 0 then { s with pc := target } else s.next
  | .read dst =>
      match s.input with
      | [] => { s with status := .fault }
      | value :: rest => { (s.setReg dst value).next with input := rest }
  | .write src => { s.next with outputRev := s.getReg src :: s.outputRev }
  | .halt => { s with status := .halted }

/-- Fetch from an array; halted/fault states and invalid PCs have no successor,
exactly as in the reference transition. -/
def step (code : Array Instr) (s : State w) : Option (State w) :=
  if s.status = .running then
    match code[s.pc]? with
    | none => none
    | some i => some (execInstr i s)
  else none

/-- Every executable instruction has exactly the reference instruction's
effect, including exhausted input and control flow. -/
@[simp] theorem toState_execInstr (i : Instr) (s : State w) :
    (execInstr i s).toState = Ram.execInstr i s.toState := by
  cases i <;> simp only [execInstr, Ram.execInstr, State.toState_regs,
    State.toState_mem, State.toState_input, State.toState_next,
    State.toState_setReg, State.toState_setMem, State.toState_with_pc,
    State.toState_with_status, State.toState_with_outputRev,
    State.toState_outputRev]
  · split <;> simp
  · cases hi : s.input <;> simp [State.toState_with_input, State.toState_next,
      State.toState_setReg] <;> rfl

/-- Full transition correspondence, including absence of a successor. Array
fetch changes representation only; each successful transition is one RAM step. -/
@[simp] theorem map_step (code : Array Instr) (s : State w) :
    (step code s).map State.toState = Ram.step code.toList s.toState := by
  simp only [step, Ram.step, State.toState_status, State.toState_pc,
    Array.getElem?_toList]
  split
  · cases code[s.pc]? <;> simp
  · rfl

theorem step_sound {code : Array Instr} {s t : State w}
    (h : step code s = some t) :
    Ram.step code.toList s.toState = some t.toState := by
  rw [← map_step, h]
  rfl

/-- The shared budget driver on executable storage. It retains the final
state, exact transition count, and stopping reason without decoding the state
during execution. -/
def run (code : Array Instr) (budget : Nat) (s : State w) : RunResult (State w) :=
  Runner.runWith (step code) State.status budget s

/-- The complete result agrees with the reference backend, not merely its
successful steps. Halt, fault, invalid PC, and exhausted fuel all agree. -/
@[simp] theorem map_run (code : Array Instr) (budget : Nat) (s : State w) :
    (run code budget s).map State.toState = Ram.run code.toList budget s.toState :=
  Runner.runWith_map (statusA := State.status) (statusB := Ram.State.status)
    State.toState (map_step code) (fun _ => rfl) budget s

theorem run_exec (code : Array Instr) (budget : Nat) (s : State w) :
    (run code budget s).steps ≤ budget ∧
      Exec code.toList (run code budget s).steps s.toState
        (run code budget s).state.toState :=
  Runner.runWith_exec State.toState (fun _ _ h => step_sound h) budget s

theorem run_outcome (code : Array Instr) (budget : Nat) (s : State w) :
    Runner.Outcome (step code) State.status budget (run code budget s) :=
  Runner.runWith_outcome (step code) State.status budget s

end Ram.Fast
