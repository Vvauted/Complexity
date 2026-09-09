/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Contract

/-!
# Compositional linking of independently proved source modules

Function-index renaming changes neither registers nor source states. A semantic
embedding records that each source function is present, with its calls renamed,
in the target table. Induction on measured execution then transports the entire
derivation, including recursive calls, with the same depth and exact step count.

`Program.link` keeps the left module's indices and shifts the right module past
it. Previously proved contracts can therefore be combined after linking; their
recursive bodies do not have to be proved again. Raising the reserved-register
boundary also preserves the measured count because frames remain callee-sized.
-/

namespace Ram

namespace Stmt

/-- Rename function indices only. Local registers, expressions, and observable
effects are unchanged. The same renaming is used at recursive call sites. -/
def renameCalls (ρ : Nat → Nat) : Stmt → Stmt
  | .skip => .skip
  | .assign dst value => .assign dst value
  | .store address value => .store address value
  | .seq a b => .seq (a.renameCalls ρ) (b.renameCalls ρ)
  | .ite c yes no => .ite c (yes.renameCalls ρ) (no.renameCalls ρ)
  | .while c body => .while c (body.renameCalls ρ)
  | .read dst => .read dst
  | .write value => .write value
  | .call dsts fn args => .call dsts (ρ fn) args

@[simp] theorem renameCalls_id (stmt : Stmt) : stmt.renameCalls id = stmt := by
  induction stmt <;> simp_all [renameCalls]

@[simp] theorem renameCalls_comp (stmt : Stmt) (ρ σ : Nat → Nat) :
    (stmt.renameCalls ρ).renameCalls σ = stmt.renameCalls (σ ∘ ρ) := by
  induction stmt <;> simp_all [renameCalls]

@[simp] theorem wellFormed_renameCalls (stmt : Stmt) (ρ : Nat → Nat) (locals : Nat) :
    (stmt.renameCalls ρ).WellFormed locals ↔ stmt.WellFormed locals := by
  induction stmt <;> simp_all [renameCalls, WellFormed]

end Stmt

namespace Func

/-- Relocate calls in a function while retaining its frame, arity, and ordered
result expressions. In particular, relocation cannot change its call-frame cost. -/
def renameCalls (ρ : Nat → Nat) (f : Func) : Func :=
  { f with body := f.body.renameCalls ρ }

@[simp] theorem renameCalls_params (f : Func) (ρ : Nat → Nat) :
    (f.renameCalls ρ).params = f.params := rfl

@[simp] theorem renameCalls_locals (f : Func) (ρ : Nat → Nat) :
    (f.renameCalls ρ).locals = f.locals := rfl

@[simp] theorem renameCalls_body (f : Func) (ρ : Nat → Nat) :
    (f.renameCalls ρ).body = f.body.renameCalls ρ := rfl

@[simp] theorem renameCalls_results (f : Func) (ρ : Nat → Nat) :
    (f.renameCalls ρ).results = f.results := rfl

@[simp] theorem renameCalls_id (f : Func) : f.renameCalls id = f := by
  cases f
  simp [renameCalls]

@[simp] theorem renameCalls_comp (f : Func) (ρ σ : Nat → Nat) :
    (f.renameCalls ρ).renameCalls σ = f.renameCalls (σ ∘ ρ) := by
  cases f
  simp [renameCalls]

@[simp] theorem wellFormed_renameCalls (f : Func) (ρ : Nat → Nat) :
    (f.renameCalls ρ).WellFormed ↔ f.WellFormed := by
  simp only [WellFormed, renameCalls_params, renameCalls_locals, renameCalls_body,
    renameCalls_results, Stmt.wellFormed_renameCalls]

end Func

namespace Program

/-- A semantic embedding preserves every function found in the source table,
including its renamed recursive body. Injectivity on all natural numbers is
unnecessary: unused indices carry no semantic obligation, and identical
functions may share a target entry. The standard linker below uses disjoint
injective index ranges for its two modules. -/
def Embeds (ρ : Nat → Nat) (source target : Program) : Prop :=
  ∀ ⦃fn f⦄, source[fn]? = some f → target[ρ fn]? = some (f.renameCalls ρ)

theorem Embeds.refl (program : Program) : Embeds id program program := by
  intro fn f h
  simpa using h

theorem Embeds.trans {source middle target : Program} {ρ σ : Nat → Nat}
    (h₁ : Embeds ρ source middle) (h₂ : Embeds σ middle target) :
    Embeds (σ ∘ ρ) source target := by
  intro fn f h
  simpa only [Func.renameCalls_comp] using h₂ (h₁ h)

/-- Appending declarations preserves the existing function table and its indices. -/
theorem embeds_append_left (left right : Program) : Embeds id left (left ++ right) := by
  intro fn f h
  change (left ++ right)[fn]? = some (f.renameCalls id)
  rw [Func.renameCalls_id,
    List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Link two independent function tables. Left indices stay unchanged; every
call in the right module is relocated by the left table's length. -/
def link (left right : Program) : Program :=
  left ++ right.map (Func.renameCalls (fun i => left.length + i))

@[simp] theorem link_length (left right : Program) :
    (link left right).length = left.length + right.length := by
  simp [link]

theorem embeds_link_left (left right : Program) : Embeds id left (link left right) :=
  embeds_append_left left (right.map (Func.renameCalls (fun i => left.length + i)))

theorem embeds_link_right (left right : Program) :
    Embeds (fun i => left.length + i) right (link left right) := by
  intro fn f h
  rw [link, List.getElem?_append_right (by change left.length ≤ left.length + fn; omega)]
  simp [h]

end Program

namespace Compiler

/-- Linking preserves function existence and argument/result arities at every call site. -/
theorem CallsValid.renameCalls {source target : Program} {ρ : Nat → Nat} {stmt : Stmt}
    (h : CallsValid source stmt) (embedding : Program.Embeds ρ source target) :
    CallsValid target (stmt.renameCalls ρ) := by
  induction stmt with
  | skip => trivial
  | assign => trivial
  | store => trivial
  | seq _ _ first second => exact ⟨first h.1, second h.2⟩
  | ite _ _ _ yes no => exact ⟨yes h.1, no h.2⟩
  | «while» _ _ body => exact body h
  | read => trivial
  | write => trivial
  | call =>
      obtain ⟨f, hf, ha, hresults⟩ := CallsValid.call_iff.mp h
      exact CallsValid.call_iff.mpr ⟨f.renameCalls ρ, embedding hf, ha, hresults⟩

/-- Link a prefix whose calls already use the final table with an independently
valid module. The prefix may call the appended functions; it need not be valid
against its own table alone. Only the old module's calls are relocated, and its
old entry statement is not appended to the new main statement. -/
theorem Valid.link_of_callsValid {control oldControl : Nat} {front old : Program}
    {main oldMain : Stmt}
    (oldValid : Valid oldControl old oldMain) (bound : oldControl ≤ control)
    (mainWF : main.WellFormed control)
    (mainCalls : CallsValid (Program.link front old) main)
    (prefixValid : ∀ f ∈ front, f.WellFormed ∧ f.locals ≤ control ∧
      CallsValid (Program.link front old) f.body ∧ f.results.length - 1 ≤ control) :
    Valid control (Program.link front old) main := by
  refine ⟨mainWF, mainCalls, ?_⟩
  intro f member
  change f ∈ front ++ old.map (Func.renameCalls (fun i => front.length + i)) at member
  rcases List.mem_append.mp member with inPrefix | imported
  · exact prefixValid f inPrefix
  · obtain ⟨g, inOld, rfl⟩ := List.mem_map.mp imported
    obtain ⟨formed, locals, calls, results⟩ := oldValid.2.2 g inOld
    refine ⟨?_, Nat.le_trans locals bound, ?_, Nat.le_trans results bound⟩
    · simpa only [Func.wellFormed_renameCalls] using formed
    · exact calls.renameCalls (Program.embeds_link_right front old)

/-- Two independently valid modules become a valid sequential component under
the maximum register boundary. No recursive function body is rechecked by an
execution proof; static call validity transports through the embeddings. -/
theorem Valid.link {a b : Nat} {left right : Program} {leftMain rightMain : Stmt}
    (hl : Valid a left leftMain) (hr : Valid b right rightMain) :
    Valid (max a b) (Program.link left right)
      (.seq leftMain (rightMain.renameCalls (fun i => left.length + i))) := by
  have el := Program.embeds_link_left left right
  have er := Program.embeds_link_right left right
  refine ⟨⟨hl.1.mono (Nat.le_max_left a b), ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simpa using hr.1.mono (Nat.le_max_right a b)
  · simpa using hl.2.1.renameCalls el
  · exact hr.2.1.renameCalls er
  · intro f hf
    change f ∈ left ++ right.map (Func.renameCalls (fun i => left.length + i)) at hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨hwf, hlocals, hcalls, hresults⟩ := hl.2.2 f hf
      refine ⟨hwf, Nat.le_trans hlocals (Nat.le_max_left a b), ?_,
        Nat.le_trans hresults (Nat.le_max_left a b)⟩
      simpa using hcalls.renameCalls el
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨hwf, hlocals, hcalls, hresults⟩ := hr.2.2 g hg
      refine ⟨?_, Nat.le_trans hlocals (Nat.le_max_right a b), ?_,
        Nat.le_trans hresults (Nat.le_max_right a b)⟩
      · simpa using hwf
      · exact hcalls.renameCalls er

end Compiler

namespace Expr

/-- Enlarging the declared source heap preserves every previously permitted
read, including reads used to compute another read's address. -/
theorem ReadsBelow.mono_heap {e : Expr} {heapLimit heapLimit' : Nat}
    {regs : Reg → Word w} {mem : Word w → Word w}
    (h : e.ReadsBelow heapLimit regs mem) (hle : heapLimit ≤ heapLimit') :
    e.ReadsBelow heapLimit' regs mem := by
  induction e with
  | const => trivial
  | var => trivial
  | bin _ _ _ left right => exact ⟨left h.1, right h.2⟩
  | load _ address => exact ⟨address h.1, Nat.lt_of_lt_of_le h.2 hle⟩

end Expr

namespace Source

/-- Heap capacity is a safety upper bound, not a runtime price. Increasing it
preserves the complete execution and its exact count, also inside recursion. -/
theorem LocalMeasuredExec.mono_heap {control heapLimit heapLimit' depth steps : Nat}
    {program : Program} {stmt : Stmt} {s t : State w}
    (h : LocalMeasuredExec control program heapLimit depth stmt steps s t)
    (hle : heapLimit ≤ heapLimit') :
    LocalMeasuredExec control program heapLimit' depth stmt steps s t := by
  induction h with
  | skip => exact .skip
  | assign reads => exact .assign (reads.mono_heap hle)
  | store addressReads valueReads destination =>
      exact .store (addressReads.mono_heap hle) (valueReads.mono_heap hle)
        (Nat.lt_of_lt_of_le destination hle)
  | seq _ _ first second => exact .seq first second
  | iteTrue reads condition _ body => exact .iteTrue (reads.mono_heap hle) condition body
  | iteFalse reads condition _ body => exact .iteFalse (reads.mono_heap hle) condition body
  | whileFalse reads condition => exact .whileFalse (reads.mono_heap hle) condition
  | whileTrue reads condition _ _ body rest =>
      exact .whileTrue (reads.mono_heap hle) condition body rest
  | read available => exact .read available
  | write reads => exact .write (reads.mono_heap hle)
  | call lookup arity hresultCount frame arguments _ results body =>
      exact .call lookup arity hresultCount frame
        (fun arg ha => (arguments arg ha).mono_heap hle)
        body (fun result hr => (results result hr).mono_heap hle)

theorem SafeExec.mono_heap {heapLimit heapLimit' depth : Nat} {program : Program}
    {stmt : Stmt} {s t : State w} (h : SafeExec program heapLimit depth stmt s t)
    (hle : heapLimit ≤ heapLimit') : SafeExec program heapLimit' depth stmt s t := by
  obtain ⟨steps, hx⟩ := h.exists_localMeasured 0
  exact (hx.mono_heap hle).erase

/-- A table embedding transports the complete measured execution, including
recursive calls, without changing its states, depth, or exact transition count. -/
theorem LocalMeasuredExec.renameCalls {control heapLimit depth steps : Nat}
    {source target : Program} {ρ : Nat → Nat} {stmt : Stmt} {s t : State w}
    (h : LocalMeasuredExec control source heapLimit depth stmt steps s t)
    (embedding : Program.Embeds ρ source target) :
    LocalMeasuredExec control target heapLimit depth (stmt.renameCalls ρ) steps s t := by
  induction h with
  | skip => exact .skip
  | assign reads =>
      simpa only [Stmt.renameCalls, LocalCompiler.stmtSize, LocalCompiler.compileStmt] using
        (LocalMeasuredExec.assign (program := target) reads)
  | store addressReads valueReads destination =>
      simpa only [Stmt.renameCalls, LocalCompiler.stmtSize, LocalCompiler.compileStmt] using
        (LocalMeasuredExec.store (program := target) addressReads valueReads destination)
  | seq _ _ first second => exact .seq first second
  | iteTrue reads condition _ body => exact .iteTrue reads condition body
  | iteFalse reads condition _ body => exact .iteFalse reads condition body
  | whileFalse reads condition => exact .whileFalse reads condition
  | whileTrue reads condition _ _ body rest => exact .whileTrue reads condition body rest
  | read available => exact .read available
  | write reads =>
      simpa only [Stmt.renameCalls, LocalCompiler.stmtSize, LocalCompiler.compileStmt] using
        (LocalMeasuredExec.write (program := target) reads)
  | call lookup arity hresultCount frame arguments _ results body =>
      exact LocalMeasuredExec.call (f := Func.renameCalls ρ _)
        (embedding lookup) arity hresultCount frame arguments body results

/-- Reusing a module at a different global register boundary and in a larger
function table leaves its complete measured execution count unchanged. -/
theorem LocalMeasuredExec.renameCalls_rebase {control heapLimit depth steps : Nat}
    {source target : Program} {ρ : Nat → Nat} {stmt : Stmt} {s t : State w}
    (h : LocalMeasuredExec control source heapLimit depth stmt steps s t)
    (embedding : Program.Embeds ρ source target) (control' : Nat) :
    LocalMeasuredExec control' target heapLimit depth (stmt.renameCalls ρ) steps s t :=
  (h.renameCalls embedding).rebase control'

theorem SafeExec.renameCalls {heapLimit depth : Nat} {source target : Program}
    {ρ : Nat → Nat} {stmt : Stmt} {s t : State w}
    (h : SafeExec source heapLimit depth stmt s t)
    (embedding : Program.Embeds ρ source target) :
    SafeExec target heapLimit depth (stmt.renameCalls ρ) s t := by
  obtain ⟨steps, hx⟩ := h.exists_localMeasured 0
  exact (hx.renameCalls embedding).erase

/-- Preserve an already proved contract, including its exact same budget. -/
theorem Contract.renameCalls {control heapLimit depth : Nat} {source target : Program}
    {ρ : Nat → Nat} {stmt : Stmt} {P Q : State w → Prop} {bound : State w → Nat}
    (h : Contract control source heapLimit depth stmt P Q bound)
    (embedding : Program.Embeds ρ source target) :
    Contract control target heapLimit depth (stmt.renameCalls ρ) P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.renameCalls embedding, hq, hb⟩

theorem Contract.rebase {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q : State w → Prop} {bound : State w → Nat}
    (h : Contract control program heapLimit depth stmt P Q bound) (control' : Nat) :
    Contract control' program heapLimit depth stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.rebase control', hq, hb⟩

/-- Reuse a contract in a larger safe heap without increasing its budget. -/
theorem Contract.mono_heap {control heapLimit heapLimit' depth : Nat}
    {program : Program} {stmt : Stmt} {P Q : State w → Prop} {bound : State w → Nat}
    (h : Contract control program heapLimit depth stmt P Q bound)
    (hle : heapLimit ≤ heapLimit') :
    Contract control program heapLimit' depth stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.mono_heap hle, hq, hb⟩

theorem RelContract.renameCalls {control heapLimit depth : Nat} {source target : Program}
    {ρ : Nat → Nat} {stmt : Stmt} {P : State w → Prop} {Q : State w → State w → Prop}
    {bound : State w → Nat} (h : RelContract control source heapLimit depth stmt P Q bound)
    (embedding : Program.Embeds ρ source target) :
    RelContract control target heapLimit depth (stmt.renameCalls ρ) P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.renameCalls embedding, hq, hb⟩

theorem RelContract.rebase {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop} {bound : State w → Nat}
    (h : RelContract control program heapLimit depth stmt P Q bound) (control' : Nat) :
    RelContract control' program heapLimit depth stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.rebase control', hq, hb⟩

theorem RelContract.mono_heap {control heapLimit heapLimit' depth : Nat}
    {program : Program} {stmt : Stmt} {P : State w → Prop} {Q : State w → State w → Prop}
    {bound : State w → Nat} (h : RelContract control program heapLimit depth stmt P Q bound)
    (hle : heapLimit ≤ heapLimit') :
    RelContract control program heapLimit' depth stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.mono_heap hle, hq, hb⟩

end Source

end Ram
