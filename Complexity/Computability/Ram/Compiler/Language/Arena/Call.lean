/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues
import Complexity.Computability.Ram.Compiler.Language.Placement

/-!
# Receiving values after placement extension

A measured call can consume arguments under the initial placement and return
fields under a final placement that assigns addresses to newly allocated
objects. Agreement on existing objects preserves the caller's rooted locals;
the fresh result need not refer to an object in the initial heap.

The execution and its exact instruction count are the existing measured-call
rule. Only the caller-side representation is transported. Shared memory retains
the callee's effects, and registers outside the receivers retain their values.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Receive a fresh lexical result after a measured call that may extend
placement. Old rooted locals retain their representation, while the returned
value is represented directly using its final placement. -/
theorem lowerCall_measured_fresh_of_placement_agrees
    {control heapLimit depth bodySteps fn : Nat} {program : Ram.Program} {f : Func}
    {finish : Source.State w}
    {initialPlacement finalPlacement : Nat → Word w} {heap : Complexity.Language.Heap}
    (layout : RegisterMap Γ) (args : Args Γ params) (env : Env Γ)
    (entry : Source.State w) (dst : Reg) (hw : 0 < w)
    (matched : layout.Matches initialPlacement env entry.regs)
    (fits : EnvFits w (args.eval env))
    (agreed : Placement.Agrees heap initialPlacement finalPlacement)
    (rooted : env.Rooted heap) {value : Value τ}
    (invocation : Source.FunctionMeasuredExec control program heapLimit depth f
      (envWords initialPlacement (args.eval env)) bodySteps entry
      (valueWords finalPlacement value) finish)
    (lookup : program[fn]? = some f) (resultCount : fieldCount τ = f.results.length)
    (bounded : layout.Bounded dst) (resultFits : ValueFits w value) :
    let received := finish.setRegs (valueRegs τ dst) (valueWords finalPlacement value)
    Source.LocalMeasuredExec control program heapLimit (depth + 1)
        (.call (valueRegs τ dst) fn (argsExprs layout args))
        (LocalCompiler.Function.callSteps 0 f bodySteps) entry received ∧
      RegisterMap.Matches (RegisterMap.extend layout τ dst) finalPlacement (Env.cons value env)
        received.regs ∧
      ∀ r, r ∉ valueRegs τ dst → received.regs r = entry.regs r := by
  dsimp only
  have registers : finish.regs = entry.regs := invocation.erase.regs_eq
  have restored : layout.Matches finalPlacement env finish.regs := by
    rw [registers]
    exact matched.placement agreed rooted
  refine ⟨lowerCall_measured layout args env entry dst hw matched fits invocation lookup resultCount,
    restored.setRegs bounded value resultFits, ?_⟩
  intro r outside
  exact (Source.State.setRegs_ne finish _ _ r outside).trans (congrFun registers r)

end Ram.LanguageCompiler
