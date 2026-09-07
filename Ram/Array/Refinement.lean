/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Model
import Ram.Array.Observation
import Ram.Verification.Observation

/-!
# List specifications on compiled RAM memory

The output representation of a `Refines` theorem can be the existing `ArrayAt`.
Its ordinary Lean function then describes the actual final memory contents,
including after checked compilation. A separate time bound retains this same
result; source/target heap agreement supplies the representation bridge.
-/

namespace Ram.Source.Refines

variable {α : Type*} {control heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {inputRep : α → State w → Prop} {base : Word w} {f : α → List (Word w)}

/-- The represented result is the standard list view of the final source heap. -/
theorem arrayContents
    (h : Refines program heapLimit depth stmt inputRep (ArrayAt heapLimit base) f) (x : α) :
    TotalContract program heapLimit depth stmt (inputRep x)
      (fun t => Ram.arrayContents t.mem base (f x).length = f x) :=
  (h x).mono_post (fun _ represented => represented.contents_eq)

/-- The ordinary Lean result describes the actual halted target memory.
No instruction bound is needed to prove this functional result. -/
theorem compile_arrayContents {code : Code} {input : List (Word w)}
    (h : Refines program heapLimit depth stmt inputRep (ArrayAt heapLimit base) f) (x : α)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : inputRep x (State.initial input)) :
    ∃ target steps,
      Ram.Exec code steps (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) target ∧
      target.status = .halted ∧ Ram.arrayContents target.mem base (f x).length = f x := by
  exact h.compile_observed x
    (fun _ _ _ represented observed => (observed.array represented).contents_eq)
    hcompile hcodefit hstackfit hp

/-- A separate count proof gives a time-bounded target execution with that
same list result, including the compiler prologue and halt instructions. -/
theorem compile_arrayContents_with_timeBound {code : Code} {input : List (Word w)}
    {bound : State w → Nat}
    (h : Refines program heapLimit depth stmt inputRep (ArrayAt heapLimit base) f) (x : α)
    (cost : TimeBound control program heapLimit depth stmt (inputRep x) bound)
    (hcompile : LocalCompiler.compileChecked control program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize control < 2 ^ w)
    (hp : inputRep x (State.initial input)) :
    ∃ target,
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) target ∧
      Ram.arrayContents target.mem base (f x).length = f x := by
  exact h.compile_observed_with_timeBound x cost
    (fun _ _ _ represented observed => (observed.array represented).contents_eq)
    hcompile hcodefit hstackfit hp

end Ram.Source.Refines
