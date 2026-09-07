/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Compiler
import Ram.LocalABI

/-!
# Linking concrete code with callee-sized local frames

The reserved registers and scratch area remain above `control`. Each call
saves and initializes only the local-register bound of its actual callee, and
each return restores that same bound. The bound table is extracted from the
program's function declarations by the checked linker, never supplied by a
user as a cost annotation.

This module proves code generation and layout. Execution simulation is a
separate obligation: layout alone does not establish semantic preservation or
a runtime bound. The original compiler remains available during migration.
-/

namespace Ram.LocalCompiler

/-- The checked linker obtains frame sizes from the program itself. The zero
default only makes the unchecked construction total; existing validity rejects
every call whose function index is absent. -/
def calleeLocals (program : Program) (fn : Nat) : Nat :=
  ((program[fn]?).map Func.locals).getD 0

@[simp] theorem calleeLocals_lookup {program : Program} {fn : Nat} {f : Func}
    (h : program[fn]? = some f) : calleeLocals program fn = f.locals := by
  simp [calleeLocals, h]

def compileStmt (control : Nat) (localsTable entries : Nat → Nat) : Stmt → Nat → Code
  | .skip, _ => []
  | .assign dst value, _ =>
      value.compile (ABI.scratch control) ++ [.move dst (ABI.scratch control)]
  | .store address value, _ =>
      address.compile (ABI.scratch control) ++ value.compile (ABI.scratch control + 1) ++
        [.store (ABI.scratch control) (ABI.scratch control + 1)]
  | .seq first second, base =>
      let firstCode := compileStmt control localsTable entries first base
      firstCode ++ compileStmt control localsTable entries second (base + firstCode.length)
  | .ite condition yes no, base =>
      let condCode := condition.compile (ABI.scratch control)
      let yesCode := compileStmt control localsTable entries yes (base + condCode.length + 1)
      let noCode := compileStmt control localsTable entries no
        (base + condCode.length + yesCode.length + 2)
      ifCode condCode (ABI.scratch control) yesCode noCode base
  | .while condition body, base =>
      let condCode := condition.compile (ABI.scratch control)
      let bodyCode := compileStmt control localsTable entries body (base + condCode.length + 1)
      whileCode condCode (ABI.scratch control) bodyCode base
  | .read dst, _ => [.read dst]
  | .write value, _ => value.compile (ABI.scratch control) ++ [.write (ABI.scratch control)]
  | .call dst fn args, base =>
      ABI.callCodeLocals control (localsTable fn) (entries fn) dst args base

/-- Increasing the global reserved-register boundary only changes register
numbers, not code length. The fixed callee table controls actual frame work. -/
theorem compileStmt_length_control_eq (localsTable : Nat → Nat) (stmt : Stmt)
    (controlA controlB : Nat) (entriesA entriesB : Nat → Nat) (baseA baseB : Nat) :
    (compileStmt controlA localsTable entriesA stmt baseA).length =
      (compileStmt controlB localsTable entriesB stmt baseB).length := by
  have he (e : Expr) (r : Reg) : (e.compile r).length = (e.compile 0).length :=
    e.compile_length_eq r 0
  induction stmt generalizing controlA controlB entriesA entriesB baseA baseB with
  | skip => rfl
  | assign => simp only [compileStmt, List.length_append, List.length_singleton, he]
  | store => simp only [compileStmt, List.length_append, List.length_singleton, he]
  | seq first second ihFirst ihSecond =>
      have hf := ihFirst controlA controlB entriesA entriesB baseA baseB
      have hs := ihSecond controlA controlB entriesA entriesB
        (baseA + (compileStmt controlA localsTable entriesA first baseA).length)
        (baseB + (compileStmt controlB localsTable entriesB first baseB).length)
      simp only [compileStmt, List.length_append]
      omega
  | ite condition yes no ihYes ihNo =>
      have hy := ihYes controlA controlB entriesA entriesB
        (baseA + (condition.compile (ABI.scratch controlA)).length + 1)
        (baseB + (condition.compile (ABI.scratch controlB)).length + 1)
      have hn := ihNo controlA controlB entriesA entriesB
        (baseA + (condition.compile (ABI.scratch controlA)).length +
          (compileStmt controlA localsTable entriesA yes
            (baseA + (condition.compile (ABI.scratch controlA)).length + 1)).length + 2)
        (baseB + (condition.compile (ABI.scratch controlB)).length +
          (compileStmt controlB localsTable entriesB yes
            (baseB + (condition.compile (ABI.scratch controlB)).length + 1)).length + 2)
      simp only [compileStmt, ifCode_length]
      have hc := he condition (ABI.scratch controlA)
      have hc' := he condition (ABI.scratch controlB)
      omega
  | «while» condition body ih =>
      have hb := ih controlA controlB entriesA entriesB
        (baseA + (condition.compile (ABI.scratch controlA)).length + 1)
        (baseB + (condition.compile (ABI.scratch controlB)).length + 1)
      simp only [compileStmt, whileCode_length]
      have hc := he condition (ABI.scratch controlA)
      have hc' := he condition (ABI.scratch controlB)
      omega
  | read => rfl
  | write => simp only [compileStmt, List.length_append, List.length_singleton, he]
  | call =>
      simp only [compileStmt, ABI.callCodeLocals_length, ABI.callPrefixLocals_length_eq, he]

/-- Relocation and function-entry resolution preserve instruction-list length. -/
theorem compileStmt_length_eq (control : Nat) (localsTable : Nat → Nat) (stmt : Stmt)
    (entriesA entriesB : Nat → Nat) (baseA baseB : Nat) :
    (compileStmt control localsTable entriesA stmt baseA).length =
      (compileStmt control localsTable entriesB stmt baseB).length :=
  compileStmt_length_control_eq localsTable stmt control control entriesA entriesB baseA baseB

/-- Static size is defined by the generated code, not by an operation-price table. -/
def stmtSize (control : Nat) (localsTable : Nat → Nat) (stmt : Stmt) : Nat :=
  (compileStmt control localsTable (fun _ => 0) stmt 0).length

@[simp] theorem compileStmt_length (control : Nat) (localsTable entries : Nat → Nat)
    (stmt : Stmt) (base : Nat) :
    (compileStmt control localsTable entries stmt base).length = stmtSize control localsTable stmt :=
  compileStmt_length_eq control localsTable stmt entries (fun _ => 0) base 0

theorem stmtSize_control_eq (localsTable : Nat → Nat) (stmt : Stmt) (a b : Nat) :
    stmtSize a localsTable stmt = stmtSize b localsTable stmt :=
  compileStmt_length_control_eq localsTable stmt a b (fun _ => 0) (fun _ => 0) 0 0

theorem stmtSize_call (control : Nat) (localsTable : Nat → Nat)
    (dst fn : Nat) (args : List Expr) :
    stmtSize control localsTable (.call dst fn args) =
      (ABI.callPrefixLocals control (localsTable fn) args 0).length + 2 := by
  simp only [stmtSize, compileStmt, ABI.callCodeLocals_length]

def compileFunc (control : Nat) (localsTable entries : Nat → Nat) (f : Func)
    (base : Nat) : Code :=
  compileStmt control localsTable entries f.body base ++
    ABI.returnCodeLocals control f.locals f.result

def funcSize (control : Nat) (localsTable : Nat → Nat) (f : Func) : Nat :=
  stmtSize control localsTable f.body + (ABI.returnCodeLocals control f.locals f.result).length

@[simp] theorem compileFunc_length (control : Nat) (localsTable entries : Nat → Nat)
    (f : Func) (base : Nat) :
    (compileFunc control localsTable entries f base).length = funcSize control localsTable f := by
  simp [compileFunc, funcSize]

theorem funcSize_control_eq (localsTable : Nat → Nat) (f : Func) (a b : Nat) :
    funcSize a localsTable f = funcSize b localsTable f := by
  simp only [funcSize, ABI.returnCodeLocals_length,
    stmtSize_control_eq localsTable f.body a b,
    Expr.compile_length_eq f.result (ABI.scratch a) (ABI.scratch b)]

/-- Emit every function once. Recursive calls use its linked entry, rather
than causing compile-time unfolding. -/
def compileFuncs (control : Nat) (localsTable entries : Nat → Nat) : Program → Nat → Code
  | [], _ => []
  | f :: fs, base =>
      compileFunc control localsTable entries f base ++
        compileFuncs control localsTable entries fs (base + funcSize control localsTable f)

@[simp] theorem compileFuncs_length (control : Nat) (localsTable entries : Nat → Nat)
    (program : Program) (base : Nat) :
    (compileFuncs control localsTable entries program base).length =
      (program.map (funcSize control localsTable)).sum := by
  induction program generalizing base with
  | nil => rfl
  | cons f fs ih => simp [compileFuncs, ih]

def prefixSize (control : Nat) (localsTable : Nat → Nat) (program : Program)
    (index : Nat) : Nat :=
  ((program.take index).map (funcSize control localsTable)).sum

@[simp] theorem prefixSize_zero (control : Nat) (localsTable : Nat → Nat) (program : Program) :
    prefixSize control localsTable program 0 = 0 := rfl

@[simp] theorem prefixSize_cons_succ (control : Nat) (localsTable : Nat → Nat)
    (f : Func) (fs : Program) (i : Nat) :
    prefixSize control localsTable (f :: fs) (i + 1) =
      funcSize control localsTable f + prefixSize control localsTable fs i := by
  simp [prefixSize]

/-- Lookup in the original function table identifies the corresponding actual
contiguous block in a linked list, including recursive/forward declarations. -/
theorem compileFuncs_codeAt {control : Nat} {localsTable entries : Nat → Nat}
    {program : Program} {base : Nat} {code : Code} {index : Nat} {f : Func}
    (hAt : CodeAt code base (compileFuncs control localsTable entries program base))
    (hlookup : program[index]? = some f) :
    CodeAt code (base + prefixSize control localsTable program index)
      (compileFunc control localsTable entries f
        (base + prefixSize control localsTable program index)) := by
  induction program generalizing base index with
  | nil => simp at hlookup
  | cons g gs ih =>
      change CodeAt code base
        (compileFunc control localsTable entries g base ++
          compileFuncs control localsTable entries gs
            (base + funcSize control localsTable g)) at hAt
      cases index with
      | zero =>
          have hgf : g = f := by simpa using hlookup
          subst g
          simpa using hAt.append_left
      | succ index =>
          have ht : CodeAt code (base + funcSize control localsTable g)
              (compileFuncs control localsTable entries gs
                (base + funcSize control localsTable g)) := by
            simpa only [compileFunc_length] using hAt.append_right
          have hf : gs[index]? = some f := by simpa using hlookup
          simpa [Nat.add_assoc] using ih ht hf

def functionsBase (control : Nat) (localsTable : Nat → Nat) (main : Stmt) : Nat :=
  1 + stmtSize control localsTable main + 1

def entry (control : Nat) (program : Program) (main : Stmt) (fn : Nat) : Nat :=
  functionsBase control (calleeLocals program) main +
    prefixSize control (calleeLocals program) program fn

/-- All call-frame bounds and return-frame bounds are obtained from the same
function declarations. Only reserved register placement uses the global bound. -/
def rawLink (control : Nat) (program : Program) (main : Stmt) : Code :=
  .read (ABI.sp control) ::
    (compileStmt control (calleeLocals program) (entry control program main) main 1 ++
      .halt :: compileFuncs control (calleeLocals program) (entry control program main)
        program (functionsBase control (calleeLocals program) main))

@[simp] theorem rawLink_prologue (control : Nat) (program : Program) (main : Stmt) :
    (rawLink control program main)[0]? = some (.read (ABI.sp control)) := rfl

theorem rawLink_main (control : Nat) (program : Program) (main : Stmt) :
    CodeAt (rawLink control program main) 1
      (compileStmt control (calleeLocals program) (entry control program main) main 1) := by
  exact CodeAt.prefix_append [.read (ABI.sp control)] _ _

theorem rawLink_halt (control : Nat) (program : Program) (main : Stmt) :
    (rawLink control program main)[1 + stmtSize control (calleeLocals program) main]? =
      some .halt := by
  have h := (CodeAt.refl (rawLink control program main)).tail
  change CodeAt (rawLink control program main) 1
    (compileStmt control (calleeLocals program) (entry control program main) main 1 ++
      .halt :: compileFuncs control (calleeLocals program) (entry control program main)
        program (functionsBase control (calleeLocals program) main)) at h
  simpa only [compileStmt_length] using h.append_right.head

theorem rawLink_functions (control : Nat) (program : Program) (main : Stmt) :
    CodeAt (rawLink control program main) (functionsBase control (calleeLocals program) main)
      (compileFuncs control (calleeLocals program) (entry control program main)
        program (functionsBase control (calleeLocals program) main)) := by
  have h := (CodeAt.refl (rawLink control program main)).tail
  change CodeAt (rawLink control program main) 1
    (compileStmt control (calleeLocals program) (entry control program main) main 1 ++
      .halt :: compileFuncs control (calleeLocals program) (entry control program main)
        program (functionsBase control (calleeLocals program) main)) at h
  simpa only [compileStmt_length, functionsBase] using h.append_right.tail

theorem rawLink_function {control : Nat} {program : Program} {main : Stmt}
    {fn : Nat} {f : Func} (hlookup : program[fn]? = some f) :
    CodeAt (rawLink control program main) (entry control program main fn)
      (compileFunc control (calleeLocals program) (entry control program main) f
        (entry control program main fn)) := by
  exact compileFuncs_codeAt (rawLink_functions control program main) hlookup

/-- The total layout size includes the one-word header read and final halt. -/
theorem rawLink_length (control : Nat) (program : Program) (main : Stmt) :
    (rawLink control program main).length =
      1 + stmtSize control (calleeLocals program) main + 1 +
        (program.map (funcSize control (calleeLocals program))).sum := by
  simp only [rawLink, List.length_cons, List.length_append, compileStmt_length,
    compileFuncs_length]
  omega

/-- The same program has the same linked size when only the reserved-register
boundary is enlarged. No function pays for unused global locals. -/
theorem rawLink_length_control_eq (program : Program) (main : Stmt) (a b : Nat) :
    (rawLink a program main).length = (rawLink b program main).length := by
  have hf : funcSize a (calleeLocals program) = funcSize b (calleeLocals program) :=
    funext fun f => funcSize_control_eq (calleeLocals program) f a b
  simp only [rawLink_length, stmtSize_control_eq (calleeLocals program) main a b, hf]

/-- The optimized linker uses exactly the existing source validity conditions. -/
abbrev Valid := Compiler.Valid

theorem calleeLocals_le {control : Nat} {program : Program} {main : Stmt}
    (hvalid : Valid control program main) (fn : Nat) : calleeLocals program fn ≤ control := by
  cases hlookup : program[fn]? with
  | none => simp [calleeLocals, hlookup]
  | some f =>
      rw [calleeLocals_lookup hlookup]
      exact (hvalid.2.2 f (List.mem_of_getElem? hlookup)).2.1

def compileChecked (control : Nat) (program : Program) (main : Stmt) : Option Code :=
  if Valid control program main then some (rawLink control program main) else none

theorem compileChecked_some_iff {control : Nat} {program : Program} {main : Stmt} {code : Code} :
    compileChecked control program main = some code ↔
      Valid control program main ∧ code = rawLink control program main := by
  by_cases h : Valid control program main <;> simp [compileChecked, h, eq_comm]

theorem compileChecked_none_iff {control : Nat} {program : Program} {main : Stmt} :
    compileChecked control program main = none ↔ ¬ Valid control program main := by
  by_cases h : Valid control program main <;> simp [compileChecked, h]

theorem compileChecked_main {control : Nat} {program : Program} {main : Stmt} {code : Code}
    (h : compileChecked control program main = some code) :
    CodeAt code 1
      (compileStmt control (calleeLocals program) (entry control program main) main 1) := by
  obtain ⟨_, rfl⟩ := compileChecked_some_iff.mp h
  exact rawLink_main control program main

theorem compileChecked_function {control : Nat} {program : Program} {main : Stmt}
    {code : Code} {fn : Nat} {f : Func}
    (h : compileChecked control program main = some code) (hlookup : program[fn]? = some f) :
    CodeAt code (entry control program main fn)
      (compileFunc control (calleeLocals program) (entry control program main) f
        (entry control program main fn)) := by
  obtain ⟨_, rfl⟩ := compileChecked_some_iff.mp h
  exact rawLink_function hlookup

end Ram.LocalCompiler
