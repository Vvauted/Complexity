/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Basic
import Complexity.Computability.Ram.Compiler.Control
import Complexity.Computability.Ram.Source.Basic

/-!
# Structured code generation and checked static linking

Every source statement, including calls and recursive calls, generates concrete
RAM code. Functions are linked once; recursion is a runtime jump through the
calling convention, never syntactic unfolding. The size functions below measure
generated code, not execution time. Execution costs still come only from `Exec`.

`compileChecked` is the public checked entry point. `rawLink` is an unchecked
construction used to state layout and subsequent simulation theorems; callers
must not treat its existence as evidence that a source program is valid.
-/

namespace Ram.Compiler

def compileStmt (n : Nat) (entries : Nat → Nat) : Stmt → Nat → Code
  | .skip, _ => []
  | .assign dst value, _ =>
      value.compile (ABI.scratch n) ++ [.move dst (ABI.scratch n)]
  | .store address value, _ =>
      address.compile (ABI.scratch n) ++ value.compile (ABI.scratch n + 1) ++
        [.store (ABI.scratch n) (ABI.scratch n + 1)]
  | .seq first second, base =>
      let firstCode := compileStmt n entries first base
      firstCode ++ compileStmt n entries second (base + firstCode.length)
  | .ite condition yes no, base =>
      let condCode := condition.compile (ABI.scratch n)
      let yesCode := compileStmt n entries yes (base + condCode.length + 1)
      let noCode := compileStmt n entries no (base + condCode.length + yesCode.length + 2)
      ifCode condCode (ABI.scratch n) yesCode noCode base
  | .while condition body, base =>
      let condCode := condition.compile (ABI.scratch n)
      let bodyCode := compileStmt n entries body (base + condCode.length + 1)
      whileCode condCode (ABI.scratch n) bodyCode base
  | .read dst, _ => [.read dst]
  | .write value, _ => value.compile (ABI.scratch n) ++ [.write (ABI.scratch n)]
  | .call dst fn args, base => ABI.callCode n (entries fn) dst args base

/-- Relocating code or resolving different function labels changes instructions,
but not their number. This is a code-layout fact, not a running-time bound. -/
theorem compileStmt_length_eq (n : Nat) (stmt : Stmt)
    (entriesA entriesB : Nat → Nat) (baseA baseB : Nat) :
    (compileStmt n entriesA stmt baseA).length =
      (compileStmt n entriesB stmt baseB).length := by
  induction stmt generalizing entriesA entriesB baseA baseB with
  | skip => rfl
  | assign => rfl
  | store => rfl
  | seq first second ihFirst ihSecond =>
      have hf := ihFirst entriesA entriesB baseA baseB
      have hs := ihSecond entriesA entriesB
        (baseA + (compileStmt n entriesA first baseA).length)
        (baseB + (compileStmt n entriesB first baseB).length)
      simp only [compileStmt, List.length_append]
      omega
  | ite condition yes no ihYes ihNo =>
      have hy := ihYes entriesA entriesB
        (baseA + (condition.compile (ABI.scratch n)).length + 1)
        (baseB + (condition.compile (ABI.scratch n)).length + 1)
      have hn := ihNo entriesA entriesB
        (baseA + (condition.compile (ABI.scratch n)).length +
          (compileStmt n entriesA yes
            (baseA + (condition.compile (ABI.scratch n)).length + 1)).length + 2)
        (baseB + (condition.compile (ABI.scratch n)).length +
          (compileStmt n entriesB yes
            (baseB + (condition.compile (ABI.scratch n)).length + 1)).length + 2)
      simp only [compileStmt, ifCode_length]
      omega
  | «while» condition body ih =>
      have hb := ih entriesA entriesB
        (baseA + (condition.compile (ABI.scratch n)).length + 1)
        (baseB + (condition.compile (ABI.scratch n)).length + 1)
      simp only [compileStmt, whileCode_length]
      omega
  | read => rfl
  | write => rfl
  | call => simp only [compileStmt, ABI.callCode_length]

/-- Static code size, obtained by generating the code at arbitrary labels. -/
def stmtSize (n : Nat) (stmt : Stmt) : Nat :=
  (compileStmt n (fun _ => 0) stmt 0).length

@[simp] theorem compileStmt_length (n : Nat) (entries : Nat → Nat)
    (stmt : Stmt) (base : Nat) :
    (compileStmt n entries stmt base).length = stmtSize n stmt :=
  compileStmt_length_eq n stmt entries (fun _ => 0) base 0

def compileFunc (n : Nat) (entries : Nat → Nat) (f : Func) (base : Nat) : Code :=
  compileStmt n entries f.body base ++ ABI.returnCode n f.result

def funcSize (n : Nat) (f : Func) : Nat :=
  stmtSize n f.body + (ABI.returnCode n f.result).length

@[simp] theorem compileFunc_length (n : Nat) (entries : Nat → Nat)
    (f : Func) (base : Nat) : (compileFunc n entries f base).length = funcSize n f := by
  simp [compileFunc, funcSize]

/-- All function bodies are emitted exactly once, using a fixed table of their
entry addresses. The table may therefore include self and mutual recursion. -/
def compileFuncs (n : Nat) (entries : Nat → Nat) : Program → Nat → Code
  | [], _ => []
  | f :: fs, base =>
      compileFunc n entries f base ++ compileFuncs n entries fs (base + funcSize n f)

@[simp] theorem compileFuncs_length (n : Nat) (entries : Nat → Nat)
    (program : Program) (base : Nat) :
    (compileFuncs n entries program base).length = (program.map (funcSize n)).sum := by
  induction program generalizing base with
  | nil => rfl
  | cons f fs ih => simp [compileFuncs, ih]

def prefixSize (n : Nat) (program : Program) (index : Nat) : Nat :=
  ((program.take index).map (funcSize n)).sum

@[simp] theorem prefixSize_zero (n : Nat) (program : Program) :
    prefixSize n program 0 = 0 := rfl

@[simp] theorem prefixSize_cons_succ (n : Nat) (f : Func) (fs : Program) (i : Nat) :
    prefixSize n (f :: fs) (i + 1) = funcSize n f + prefixSize n fs i := by
  simp [prefixSize]

/-- Every function lookup gives the actual contiguous block at its linked
address, inside arbitrary surrounding machine code. -/
theorem compileFuncs_codeAt {n : Nat} {entries : Nat → Nat} {program : Program}
    {base : Nat} {code : Code} {index : Nat} {f : Func}
    (hAt : CodeAt code base (compileFuncs n entries program base))
    (hlookup : program[index]? = some f) :
    CodeAt code (base + prefixSize n program index)
      (compileFunc n entries f (base + prefixSize n program index)) := by
  induction program generalizing base index with
  | nil => simp at hlookup
  | cons g gs ih =>
      change CodeAt code base
        (compileFunc n entries g base ++
          compileFuncs n entries gs (base + funcSize n g)) at hAt
      cases index with
      | zero =>
          have hgf : g = f := by simpa using hlookup
          subst g
          simpa using hAt.append_left
      | succ index =>
          have ht : CodeAt code (base + funcSize n g)
              (compileFuncs n entries gs (base + funcSize n g)) := by
            simpa only [compileFunc_length] using hAt.append_right
          have hf : gs[index]? = some f := by simpa using hlookup
          simpa [Nat.add_assoc] using ih ht hf

/-- One prologue instruction and the main block precede the halt instruction;
all callable functions are placed after that halt. -/
def functionsBase (n : Nat) (main : Stmt) : Nat := 1 + stmtSize n main + 1

def entry (n : Nat) (program : Program) (main : Stmt) (fn : Nat) : Nat :=
  functionsBase n main + prefixSize n program fn

/-- Unchecked internal linking construction. Use `compileChecked` to reject
missing functions, wrong arities, and invalid local-register bounds. The first
input word initializes SP to the externally specified heap/stack boundary. -/
def rawLink (n : Nat) (program : Program) (main : Stmt) : Code :=
  .read (ABI.sp n) ::
    (compileStmt n (entry n program main) main 1 ++
      .halt :: compileFuncs n (entry n program main) program (functionsBase n main))

@[simp] theorem rawLink_prologue (n : Nat) (program : Program) (main : Stmt) :
    (rawLink n program main)[0]? = some (.read (ABI.sp n)) := rfl

theorem rawLink_main (n : Nat) (program : Program) (main : Stmt) :
    CodeAt (rawLink n program main) 1
      (compileStmt n (entry n program main) main 1) := by
  exact CodeAt.prefix_append [.read (ABI.sp n)] _ _

theorem rawLink_halt (n : Nat) (program : Program) (main : Stmt) :
    (rawLink n program main)[1 + stmtSize n main]? = some .halt := by
  have h := (CodeAt.refl (rawLink n program main)).tail
  change CodeAt (rawLink n program main) 1
    (compileStmt n (entry n program main) main 1 ++
      .halt :: compileFuncs n (entry n program main) program (functionsBase n main)) at h
  simpa only [compileStmt_length] using h.append_right.head

theorem rawLink_functions (n : Nat) (program : Program) (main : Stmt) :
    CodeAt (rawLink n program main) (functionsBase n main)
      (compileFuncs n (entry n program main) program (functionsBase n main)) := by
  have h := (CodeAt.refl (rawLink n program main)).tail
  change CodeAt (rawLink n program main) 1
    (compileStmt n (entry n program main) main 1 ++
      .halt :: compileFuncs n (entry n program main) program (functionsBase n main)) at h
  simpa only [compileStmt_length, functionsBase] using h.append_right.tail

theorem rawLink_function {n : Nat} {program : Program} {main : Stmt}
    {fn : Nat} {f : Func} (hlookup : program[fn]? = some f) :
    CodeAt (rawLink n program main) (entry n program main fn)
      (compileFunc n (entry n program main) f (entry n program main fn)) := by
  exact compileFuncs_codeAt (rawLink_functions n program main) hlookup

/-- Function existence and arity are checked at every call site, including
inside all function bodies. This finite check does not unfold recursive calls. -/
def CallsValid (program : Program) : Stmt → Prop
  | .skip | .assign _ _ | .store _ _ | .read _ | .write _ => True
  | .seq first second => CallsValid program first ∧ CallsValid program second
  | .ite _ yes no => CallsValid program yes ∧ CallsValid program no
  | .while _ body => CallsValid program body
  | .call _ fn args =>
      match program[fn]? with
      | none => False
      | some f => args.length = f.params

instance instDecidableCallsValid (program : Program) :
    (stmt : Stmt) → Decidable (CallsValid program stmt)
  | .skip | .assign _ _ | .store _ _ | .read _ | .write _ => isTrue trivial
  | .seq first second =>
      @instDecidableAnd _ _ (instDecidableCallsValid program first)
        (instDecidableCallsValid program second)
  | .ite _ yes no =>
      @instDecidableAnd _ _ (instDecidableCallsValid program yes)
        (instDecidableCallsValid program no)
  | .while _ body => instDecidableCallsValid program body
  | .call dst fn args =>
      match h : program[fn]? with
      | none => isFalse (by simp [CallsValid, h])
      | some f =>
          if ha : args.length = f.params then isTrue (by simpa [CallsValid, h] using ha)
          else isFalse (by simpa [CallsValid, h] using ha)

theorem CallsValid.call_iff {program : Program} {dst fn : Nat} {args : List Expr} :
    CallsValid program (.call dst fn args) ↔
      ∃ f, program[fn]? = some f ∧ args.length = f.params := by
  cases h : program[fn]? <;> simp [CallsValid, h]

instance instDecidableStmtWellFormed :
    (stmt : Stmt) → (n : Nat) → Decidable (stmt.WellFormed n)
  | .skip, _ => isTrue trivial
  | .assign dst value, n =>
      inferInstanceAs (Decidable (dst < n ∧ value.Bounded n))
  | .store address value, n =>
      inferInstanceAs (Decidable (address.Bounded n ∧ value.Bounded n))
  | .seq first second, n =>
      @instDecidableAnd _ _ (instDecidableStmtWellFormed first n)
        (instDecidableStmtWellFormed second n)
  | .ite condition yes no, n =>
      @instDecidableAnd _ _ (Expr.instDecidableBounded condition n)
        (@instDecidableAnd _ _ (instDecidableStmtWellFormed yes n)
          (instDecidableStmtWellFormed no n))
  | .while condition body, n =>
      @instDecidableAnd _ _ (Expr.instDecidableBounded condition n)
        (instDecidableStmtWellFormed body n)
  | .read dst, n => inferInstanceAs (Decidable (dst < n))
  | .write value, n => Expr.instDecidableBounded value n
  | .call dst _ args, n =>
      inferInstanceAs (Decidable (dst < n ∧ ∀ arg ∈ args, arg.Bounded n))

instance instDecidableFuncWellFormed (f : Func) : Decidable f.WellFormed :=
  inferInstanceAs (Decidable
    (f.params ≤ f.locals ∧ f.body.WellFormed f.locals ∧ f.result.Bounded f.locals))

/-- Static validity of the entire linked program. Heap/stack separation and
word-width bounds are runtime proof obligations, not established by this check. -/
def Valid (n : Nat) (program : Program) (main : Stmt) : Prop :=
  main.WellFormed n ∧ CallsValid program main ∧
    ∀ f ∈ program, f.WellFormed ∧ f.locals ≤ n ∧ CallsValid program f.body

instance instDecidableValid (n : Nat) (program : Program) (main : Stmt) :
    Decidable (Valid n program main) :=
  inferInstanceAs (Decidable
    (main.WellFormed n ∧ CallsValid program main ∧
      ∀ f ∈ program, f.WellFormed ∧ f.locals ≤ n ∧ CallsValid program f.body))

/-- Checked source-to-code entry point. Invalid calls and local frames are
rejected before an executable is returned; there is no fallback jump address. -/
def compileChecked (n : Nat) (program : Program) (main : Stmt) : Option Code :=
  if Valid n program main then some (rawLink n program main) else none

theorem compileChecked_some_iff {n : Nat} {program : Program} {main : Stmt} {code : Code} :
    compileChecked n program main = some code ↔
      Valid n program main ∧ code = rawLink n program main := by
  by_cases h : Valid n program main <;> simp [compileChecked, h, eq_comm]

theorem compileChecked_none_iff {n : Nat} {program : Program} {main : Stmt} :
    compileChecked n program main = none ↔ ¬ Valid n program main := by
  by_cases h : Valid n program main <;> simp [compileChecked, h]

theorem compileChecked_main {n : Nat} {program : Program} {main : Stmt} {code : Code}
    (h : compileChecked n program main = some code) :
    CodeAt code 1 (compileStmt n (entry n program main) main 1) := by
  obtain ⟨_, rfl⟩ := compileChecked_some_iff.mp h
  exact rawLink_main n program main

theorem compileChecked_function {n : Nat} {program : Program} {main : Stmt}
    {code : Code} {fn : Nat} {f : Func}
    (h : compileChecked n program main = some code) (hlookup : program[fn]? = some f) :
    CodeAt code (entry n program main fn)
      (compileFunc n (entry n program main) f (entry n program main fn)) := by
  obtain ⟨_, rfl⟩ := compileChecked_some_iff.mp h
  exact rawLink_function hlookup

end Ram.Compiler
