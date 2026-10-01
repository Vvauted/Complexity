/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program
import Complexity.Computability.Ram.Compiler.Language.Session

/-!
# Uniform RAM time for persistent source callbacks

The configuration uses the existing fixed Program.Input and RamInput layout.
Its initial heap and machine memory depend only on that configuration, never on
the future request history or a candidate-selected mathematical state encoder.
Initialization and every subsequent callback belong to one source Session;
RAM.Session.Runs retains their actual returned states, heaps, placements and
cursors and sums their actual compiled invocation counts.

As for Program.TimeO, one global multiplier adjusts the fixed logarithmic width
scale. Here the scale depends only on configuration. This interface therefore
requires request word ranges to be supported at configuration-admitted widths;
it does not claim to support arbitrary unbounded streams at one fixed width.
The request encoding is a fixed public port presentation, chosen before the
candidate. It is not a loader, free preprocessing algorithm or heap allocator.
Reference-bearing requests need a separate justified loading protocol.

These are preloaded init-and-callback bounds, including the actual call/return
wrappers and halts. Initial input preparation, arena bootstrap, inter-call port
transport, serialization and an executable streaming driver are outside this
boundary. Correctness remains an independent source proposition. No new
evaluator, host-callback price or continuous-I/O execution model is introduced.
-/

namespace Ram.LanguageCompiler.Session

universe u

/-- The fixed configuration arena, before the actual initializer is invoked.
This uses only the registered input realization; it neither sees future
requests nor loads a candidate's private mathematical state. -/
def State.ofInput {α : Type u} [Complexity.Program.Input α]
    [Complexity.Program.RamInput α] (x : α) (w : Nat)
    (base : 1 + ArrayFunction.inputWordWidth (Complexity.Program.RamInput.words x) ≤ w) :
    State w (ArrayFunction.heapLimit w) :=
  ⟨Complexity.Program.Input.heap x, Complexity.Program.RamInput.placement x w,
    Complexity.Program.RamInput.cursor x, Complexity.Program.RamInput.entry x w,
    Complexity.Program.RamInput.arena x w base⟩

end Ram.LanguageCompiler.Session

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v} {request : List Ty} {response : Ty}

/-- Uniform bounds on actual initialized callback histories at every legal
configuration, history and admitted width. Every current request must fit the
word width, and capacity, allocation and termination must be established through
the real executions. These are conclusions, not premises that can exclude legal
inputs. The history is proof-side environment
data: each source call receives only its current encoded request and retained
actual state. Initialization is charged even for an empty history. -/
def TimeO (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (size : α → List ι → Nat) (growth : Nat → Nat) : Prop :=
  ∃ overhead : Nat, ∃ bound : Nat → Nat,
    Asymptotics.IsBigO Filter.atTop (fun n => (bound n : ℝ))
      (fun n => (growth n : ℝ)) ∧
    ∀ x inputs, valid x inputs → ∀ w, ∀ admitted : Complexity.Program.width overhead x ≤ w,
      (∀ input ∈ inputs, Ram.LanguageCompiler.EnvFits w (encode input)) ∧
      ∃ (replies : List (Value response × Heap)) (finish : Value session.stateTy)
        (finalWorld : Ram.LanguageCompiler.Session.State w
          (Ram.LanguageCompiler.ArrayFunction.heapLimit w)) (steps : Nat),
        Ram.LanguageCompiler.Session.Runs session (Complexity.Program.Input.args x)
          (Ram.LanguageCompiler.Session.State.ofInput x w
            (Complexity.Program.width_base admitted))
          (inputs.map encode) replies finish finalWorld steps ∧
        steps ≤ bound (size x inputs)

/-- State a possibly multivariate target directly on configuration and history,
using the same actual callback counts and ordinary linear asymptotic envelope.
Evaluating this proof-side scale supplies no runtime advice. -/
abbrev TimeOOn (session : Session (Complexity.Program.Input.params α) request response)
    (encode : ι → Env request) (valid : α → List ι → Prop)
    (growth : α → List ι → Nat) : Prop :=
  session.TimeO encode valid growth id

/-- Restrict the protocol's legal histories without changing its source entries,
input boundary, width multiplier, cost envelope or actual executions. -/
theorem TimeO.mono_valid
    {session : Session (Complexity.Program.Input.params α) request response}
    {encode : ι → Env request} {valid valid' : α → List ι → Prop}
    {size : α → List ι → Nat} {growth : Nat → Nat}
    (time : session.TimeO encode valid size growth)
    (restrict : ∀ x inputs, valid' x inputs → valid x inputs) :
    session.TimeO encode valid' size growth := by
  obtain ⟨overhead, bound, asymptotic, runs⟩ := time
  exact ⟨overhead, bound, asymptotic,
    fun x inputs legal => runs x inputs (restrict x inputs legal)⟩

end Complexity.Language.Session
