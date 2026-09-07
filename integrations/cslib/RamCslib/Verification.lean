/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Cslib.Foundations.Semantics.FLTS.Basic
import Cslib.Computability.Automata.DA.Basic
import Ram.Verification.Refinement

/-!
# Reusing CSLib transition models in RAM functional proofs

`Refines.flts_mtr` composes implementations of individual transitions into
CSLib's own extended transition function. The represented state is arbitrary:
it may be an automaton state, a finite map, or another mathematical model.
The proof retains terminating safe execution of the actual RAM statements.

The statement list is a finite unrolling: each supplied label contributes its
implementation to the syntax. This is not a uniform interpreter accepting
arbitrarily long inputs. `Refines.finAcc_accepts` also applies to a separately
verified uniform implementation; it transfers both acceptance and rejection
from CSLib's existing automaton semantics to an observation of the RAM result.

These are functional bridges. CSLib's transition count is not asserted to be
the RAM instruction count. Actual running-time proofs remain separate
`TimeBound` proofs for the same statement and can be joined with `Refines`.
-/

namespace Ram.Source.Refines

variable {α σ : Type*} {program : Program} {heapLimit depth : Nat}

/-- Finite sequential composition implements CSLib's extended transition
function. Individual implementation contracts need not unfold their bodies. -/
theorem flts_mtr (model : _root_.Cslib.FLTS α σ) (implementation : σ → Stmt)
    {rep : α → State w → Prop}
    (step : ∀ symbol, Refines program heapLimit depth (implementation symbol)
      rep rep (fun state => model.tr state symbol)) (symbols : List σ) :
    Refines program heapLimit depth
      (symbols.foldr (fun symbol rest => .seq (implementation symbol) rest) .skip)
      rep rep (fun state => model.mtr state symbols) := by
  induction symbols with
  | nil =>
      intro state entry represented
      exact ⟨entry, .skip, represented⟩
  | cons symbol symbols ih =>
      exact (step symbol).seq ih

/-- Reuse the automaton's acceptance specification through a concrete result
observation. The equivalence transfers rejected words as well as accepted ones. -/
theorem finAcc_accepts (model : _root_.Cslib.Automata.DA.FinAcc α σ)
    {stmt : Stmt} {inputRep : List σ → State w → Prop}
    {outputRep : α → State w → Prop}
    (h : Refines program heapLimit depth stmt inputRep outputRep
      (fun symbols => model.mtr model.start symbols))
    (accepts : State w → Prop)
    (sound : ∀ state target, outputRep state target →
      (accepts target ↔ state ∈ model.accept)) (symbols : List σ) :
    TotalContract program heapLimit depth stmt (inputRep symbols)
      (fun target => accepts target ↔
        _root_.Cslib.Automata.Acceptor.Accepts model symbols) := by
  apply (h symbols).mono_post
  intro target represented
  exact sound _ target represented

end Ram.Source.Refines
