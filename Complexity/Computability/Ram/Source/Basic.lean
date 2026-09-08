/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Expr

/-!
# Structured programs with local function frames

This language has ordinary structured control flow and first-order functions.
A call evaluates its arguments in the caller, initializes a fresh local frame,
and shares memory and input/output with its caller. Functions may call
themselves or each other. Returning evaluates every result in the callee's final
state, restores the caller's locals, and assigns the results in destination order.

`Source.Exec` describes successful finite execution. It is deliberately not a
cost semantics: a source call, expression, or loop is not one RAM instruction.
Runtime guarantees must ultimately be derived from compiled machine execution.
-/

namespace Ram

inductive Stmt where
  | skip
  | assign (dst : Reg) (value : Expr)
  | store (address value : Expr)
  | seq (first second : Stmt)
  | ite (condition : Expr) (yes no : Stmt)
  | while (condition : Expr) (body : Stmt)
  | read (dst : Reg)
  | write (value : Expr)
  | call (dsts : List Reg) (fn : Nat) (args : List Expr)
  deriving DecidableEq, Repr

/-- `locals` is the total local-register bound, including the `params`
parameter registers. Parameter `i` is passed in local register `i`.
Every expression in `results` is evaluated in the same state after the body has
completed. An empty result list represents a function returning no value. -/
structure Func where
  params : Nat
  locals : Nat
  body : Stmt
  results : List Expr
  deriving DecidableEq, Repr

abbrev Program := List Func

namespace Stmt

/-- Static local-register bounds. Function existence and arity are separate
call obligations; there are no runtime bounds checks hidden in this predicate. -/
def WellFormed (stmt : Stmt) (locals : Nat) : Prop :=
  match stmt with
  | .skip => True
  | .assign dst value => dst < locals ∧ value.Bounded locals
  | .store address value => address.Bounded locals ∧ value.Bounded locals
  | .seq first second => first.WellFormed locals ∧ second.WellFormed locals
  | .ite condition yes no =>
      condition.Bounded locals ∧ yes.WellFormed locals ∧ no.WellFormed locals
  | .while condition body => condition.Bounded locals ∧ body.WellFormed locals
  | .read dst => dst < locals
  | .write value => value.Bounded locals
  | .call dsts _ args =>
      (∀ dst ∈ dsts, dst < locals) ∧ ∀ arg ∈ args, arg.Bounded locals

end Stmt

namespace Func

def WellFormed (f : Func) : Prop :=
  f.params ≤ f.locals ∧ f.body.WellFormed f.locals ∧
    ∀ result ∈ f.results, result.Bounded f.locals

end Func

namespace Source

structure State (w : Nat) where
  regs : Reg → Word w
  mem : Word w → Word w
  input : List (Word w)
  outputRev : List (Word w)

namespace State

def initial (input : List (Word w)) : State w where
  regs := fun _ => 0
  mem := fun _ => 0
  input := input
  outputRev := []

def eval (s : State w) (e : Expr) : Word w := e.eval s.regs s.mem

def setReg (s : State w) (dst : Reg) (value : Word w) : State w :=
  { s with regs := fun r => if r = dst then value else s.regs r }

/-- Assign already evaluated values in destination order. Repeated destinations
keep their last assigned value. Calls separately require equal list lengths. -/
def setRegs (s : State w) (dsts : List Reg) (values : List (Word w)) : State w :=
  (dsts.zip values).foldl (fun t field => t.setReg field.1 field.2) s

def setMem (s : State w) (address value : Word w) : State w :=
  { s with mem := fun a => if a = address then value else s.mem a }

def output (s : State w) : List (Word w) := s.outputRev.reverse

/-- All arguments have already been evaluated in the caller. Registers beyond
the argument list start at zero; the callee shares memory and input/output. -/
def enter (s : State w) (args : List (Word w)) : State w :=
  { s with regs := fun r => args[r]?.getD 0 }

/-- Evaluate all results in the original callee's final state, restore the
caller's local frame, then receive those values in order. Callee memory and
input/output effects are retained, including when no result is returned. -/
def leave (caller callee : State w) (dsts : List Reg) (results : List Expr) : State w :=
  { callee with regs := caller.regs }.setRegs dsts (results.map callee.eval)

@[simp] theorem setReg_same (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).regs dst = value := by
  simp [setReg]

@[simp] theorem setReg_ne (s : State w) (dst r : Reg) (value : Word w)
    (h : r ≠ dst) : (s.setReg dst value).regs r = s.regs r := by
  simp [setReg, h]

@[simp] theorem setRegs_nil (s : State w) (values : List (Word w)) :
    s.setRegs [] values = s := rfl

@[simp] theorem setRegs_nil_values (s : State w) (dsts : List Reg) :
    s.setRegs dsts [] = s := by
  cases dsts <;> rfl

@[simp] theorem setRegs_cons (s : State w) (dst : Reg) (dsts : List Reg)
    (value : Word w) (values : List (Word w)) :
    s.setRegs (dst :: dsts) (value :: values) = (s.setReg dst value).setRegs dsts values :=
  rfl

@[simp] theorem setRegs_singleton (s : State w) (dst : Reg) (value : Word w) :
    s.setRegs [dst] [value] = s.setReg dst value := rfl

/-- Assigning return fields preserves every unassigned local, without requiring
the destinations to be distinct. -/
@[simp] theorem setRegs_ne (s : State w) (dsts : List Reg) (values : List (Word w))
    (r : Reg) (h : r ∉ dsts) : (s.setRegs dsts values).regs r = s.regs r := by
  induction dsts generalizing s values with
  | nil => rfl
  | cons dst dsts ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          have hne : r ≠ dst := fun heq => h (by simp [heq])
          have htail : r ∉ dsts := fun hmem => h (by simp [hmem])
          rw [setRegs_cons, ih _ _ htail, setReg_ne _ _ _ _ hne]

@[simp] theorem setRegs_mem (s : State w) (dsts : List Reg) (values : List (Word w)) :
    (s.setRegs dsts values).mem = s.mem := by
  induction dsts generalizing s values with
  | nil => rfl
  | cons dst dsts ih =>
      cases values with
      | nil => rfl
      | cons value values => simpa only [setRegs_cons] using ih (s.setReg dst value) values

@[simp] theorem setRegs_input (s : State w) (dsts : List Reg) (values : List (Word w)) :
    (s.setRegs dsts values).input = s.input := by
  induction dsts generalizing s values with
  | nil => rfl
  | cons dst dsts ih =>
      cases values with
      | nil => rfl
      | cons value values => simpa only [setRegs_cons] using ih (s.setReg dst value) values

@[simp] theorem setRegs_outputRev (s : State w) (dsts : List Reg)
    (values : List (Word w)) : (s.setRegs dsts values).outputRev = s.outputRev := by
  induction dsts generalizing s values with
  | nil => rfl
  | cons dst dsts ih =>
      cases values with
      | nil => rfl
      | cons value values => simpa only [setRegs_cons] using ih (s.setReg dst value) values

@[simp] theorem setMem_same (s : State w) (address value : Word w) :
    (s.setMem address value).mem address = value := by
  simp [setMem]

@[simp] theorem setMem_ne (s : State w) (address a value : Word w)
    (h : a ≠ address) : (s.setMem address value).mem a = s.mem a := by
  simp [setMem, h]

@[simp] theorem enter_mem (s : State w) (args : List (Word w)) :
    (s.enter args).mem = s.mem := rfl

@[simp] theorem enter_input (s : State w) (args : List (Word w)) :
    (s.enter args).input = s.input := rfl

@[simp] theorem enter_outputRev (s : State w) (args : List (Word w)) :
    (s.enter args).outputRev = s.outputRev := rfl

@[simp] theorem leave_dst (caller callee : State w) (dst : Reg) (result : Expr) :
    (caller.leave callee [dst] [result]).regs dst = callee.eval result := by
  simp [leave]

@[simp] theorem leave_ne (caller callee : State w) (dsts : List Reg) (r : Reg)
    (results : List Expr) (h : r ∉ dsts) :
    (caller.leave callee dsts results).regs r = caller.regs r := by
  simp [leave, h]

@[simp] theorem leave_mem (caller callee : State w) (dsts : List Reg) (results : List Expr) :
    (caller.leave callee dsts results).mem = callee.mem := by
  simp [leave]

@[simp] theorem leave_input (caller callee : State w) (dsts : List Reg) (results : List Expr) :
    (caller.leave callee dsts results).input = callee.input := by
  simp [leave]

@[simp] theorem leave_outputRev (caller callee : State w) (dsts : List Reg)
    (results : List Expr) : (caller.leave callee dsts results).outputRev = callee.outputRev := by
  simp [leave]

end State

/-- Successful finite execution. A true branch is any nonzero word. An empty
input stream has no successful `read` derivation. Calls check function lookup,
argument and result arities, and the parameter-frame bound, and recursively
execute the callee body.
In particular, no rule assumes termination of a recursive call. -/
inductive Exec (program : Program) : Stmt → State w → State w → Prop where
  | skip : Exec program .skip s s
  | assign : Exec program (.assign dst value) s (s.setReg dst (s.eval value))
  | store : Exec program (.store address value) s
      (s.setMem (s.eval address) (s.eval value))
  | seq (first : Exec program a s middle) (second : Exec program b middle t) :
      Exec program (.seq a b) s t
  | iteTrue (condition : s.eval c ≠ 0) (body : Exec program yes s t) :
      Exec program (.ite c yes no) s t
  | iteFalse (condition : s.eval c = 0) (body : Exec program no s t) :
      Exec program (.ite c yes no) s t
  | whileFalse (condition : s.eval c = 0) : Exec program (.while c body) s s
  | whileTrue (condition : s.eval c ≠ 0) (body : Exec program b s middle)
      (rest : Exec program (.while c b) middle t) :
      Exec program (.while c b) s t
  | read (available : s.input = value :: rest) :
      Exec program (.read dst) s { s.setReg dst value with input := rest }
  | write : Exec program (.write value) s
      { s with outputRev := s.eval value :: s.outputRev }
  | call (lookup : program[fn]? = some f) (arity : args.length = f.params)
      (hresultCount : dsts.length = f.results.length)
      (frame : f.params ≤ f.locals)
      (body : Exec program f.body (s.enter (args.map s.eval)) callee) :
      Exec program (.call dsts fn args) s (s.leave callee dsts f.results)

/-- Source-level total functional correctness. Cost is intentionally absent;
the machine compilation theorem supplies the separate execution-cost claim. -/
def TotalCorrect (program : Program) (stmt : Stmt)
    (pre : State w → Prop) (post : State w → State w → Prop) : Prop :=
  ∀ s, pre s → ∃ t, Exec program stmt s t ∧ post s t

/-- The local-frame semantics is deterministic, including recursive calls. -/
theorem Exec.deterministic {program : Program} {stmt : Stmt} {s t u : State w}
    (ht : Exec program stmt s t) (hu : Exec program stmt s u) : t = u := by
  induction ht <;> cases hu <;> grind

theorem read_empty {program : Program} {s t : State w} {dst : Reg}
    (empty : s.input = []) : ¬ Exec program (.read dst) s t := by
  intro h
  cases h with
  | read available => simp [empty] at available

theorem call_missing {program : Program} {s t : State w}
    {dsts : List Reg} {fn : Nat} {args : List Expr}
    (missing : program[fn]? = none) : ¬ Exec program (.call dsts fn args) s t := by
  intro h
  cases h with
  | call lookup _ _ _ _ => simp [missing] at lookup

end Source

end Ram
