/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Effects.Heap
import Complexity.Language.Syntax
import Complexity.Computability.Ram.Compiler.Language.Arena.ExecutionCost
import Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution
import Std.Tactic.Do

/-!
# Returning an allocated array across a call and a later allocation

`make` allocates an initialized array and returns its descriptor. `retain`
calls that actual body, allocates a second array, then reads the original
array's first cell when it is nonempty and returns the original descriptor.
The empty case returns directly. Both allocations remain in the final heap.

The mathematical result is ordinary `Array.replicate` contents, with every
old view preserved. Source termination has no capacity or time premise.
Readiness separately requires fitting values and cumulative reserved capacity;
costs compose the shared allocation, call, branch, read and return rules.
This typed source consumer adds no algorithm-specific lowering or registers.
-/

namespace Complexity.Language.Examples.Allocation

open Ram.LanguageCompiler
open scoped Part.TotalCorrectness

source_program Named where
  def make (n : Nat) (initial : Nat) : Buffer Nat := do
    let xs ← Buffer.alloc n initial
    return xs

/-- Named allocation has an ordinary native Array specification. The shared
allocation specification supplies the proof; no register or capacity appears. -/
theorem named_make_spec (n initial : Nat) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (Named.make n initial)
      (fun _ => ⟨True⟩)
      (fun buffer heap => ⟨buffer.Contents heap (Array.replicate n initial)⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)) := by
  rw [Named.make_eq]
  mvcgen
  simp_all

/-- The actual producer and caller signatures. -/
abbrev signatures : List Signature :=
  [⟨[.nat, .nat], .buffer .nat⟩, ⟨[.nat, .nat, .nat], .buffer .nat⟩]

abbrev makeId : Fin signatures.length := ⟨0, by decide⟩
abbrev retainId : Fin signatures.length := ⟨1, by decide⟩

/-- Allocate exactly the requested initialized native array and return its view. -/
def makeBody : Stmt signatures [.nat, .nat] (.buffer .nat) :=
  .alloc (.var .here) (.var (.there .here)) (.ret (.var .here))

private abbrev BranchContext : List Ty :=
  [.bool, .buffer .nat, .buffer .nat, .nat, .nat, .nat]

private def original : Atom BranchContext (.buffer .nat) := .var (.there (.there .here))

/-- The empty path returns the original descriptor without attempting a read. -/
def returnOriginal : Stmt signatures BranchContext (.buffer .nat) := .ret original

/-- The nonempty path performs an actual read before returning the original descriptor. -/
def readOriginal : Stmt signatures BranchContext (.buffer .nat) :=
  .read original (.nat 0) (.ret (.var (.there (.there (.there .here)))))

/-- Inspect the saved buffer after the second allocation, without reading an empty array. -/
def inspectBody : Stmt signatures
    [.buffer .nat, .buffer .nat, .nat, .nat, .nat] (.buffer .nat) :=
  .letPrim (.eq (.var (.there (.there .here))) (.nat 0))
    (.ite (.var .here) returnOriginal readOriginal)

/-- A second allocation uses the caller's requested extra extent. -/
def retainContinuation : Stmt signatures [.buffer .nat, .nat, .nat, .nat] (.buffer .nat) :=
  .alloc (.var (.there (.there (.there .here)))) (.nat 0) inspectBody

private def producerArgs : Args [.nat, .nat, .nat] signatures[makeId].params :=
  .cons (.var .here) (.cons (.var (.there .here)) .nil)

/-- This is a real call to `make`, followed by allocation and use of its returned buffer. -/
def retainBody : Stmt signatures [.nat, .nat, .nat] (.buffer .nat) :=
  .call makeId producerArgs retainContinuation

/-- Both bodies occupy the source function table used by the compiler. -/
def program : Program signatures where
  body := Fin.cases makeBody (Fin.cases retainBody (fun fn => Fin.elim0 fn))

def makeArgs (n initial : Nat) : Env [.nat, .nat] :=
  Env.cons n (Env.cons initial Env.empty)

def retainArgs (n initial extra : Nat) : Env [.nat, .nat, .nat] :=
  Env.cons n (Env.cons initial (Env.cons extra Env.empty))

/-- The first source allocation's actual returned handle. -/
abbrev savedBuffer (heap : Heap) (n initial : Nat) : Buffer .nat :=
  (heap.alloc (τ := .nat) n initial).1

/-- The actual source heap after both allocations, without reclamation. -/
abbrev retainedHeap (heap : Heap) (n initial extra : Nat) : Heap :=
  ((heap.alloc (τ := .nat) n initial).2.alloc (τ := .nat) extra 0).2

private def inspectState (heap : Heap) (n initial extra : Nat) :
    State [.buffer .nat, .buffer .nat, .nat, .nat, .nat] :=
  ⟨Env.cons ((heap.alloc (τ := .nat) n initial).2.alloc (τ := .nat) extra 0).1
    (Env.cons (savedBuffer heap n initial) (retainArgs n initial extra)),
    retainedHeap heap n initial extra⟩

private def branchState (heap : Heap) (n initial extra : Nat) : State BranchContext :=
  State.cons (decide (n = 0)) (inspectState heap n initial extra)

private def makeReturnState (heap : Heap) (n initial : Nat) :
    State [.buffer .nat, .nat, .nat] :=
  State.cons (savedBuffer heap n initial)
    ⟨makeArgs n initial, (heap.alloc (τ := .nat) n initial).2⟩

private def afterCallState (heap : Heap) (n initial extra : Nat) :
    State [.buffer .nat, .nat, .nat, .nat] :=
  State.cons (savedBuffer heap n initial)
    ⟨retainArgs n initial extra, (heap.alloc (τ := .nat) n initial).2⟩

/-- The second allocation does not change the first array's mathematical contents. -/
theorem retained_contents (heap : Heap) (n initial extra : Nat) :
    (savedBuffer heap n initial).Contents (retainedHeap heap n initial extra)
      (Array.replicate n initial) :=
  (heap.alloc_contents (τ := .nat) n initial).alloc (τ := .nat) extra 0

/-- A nonempty returned array is really read from the heap after the later allocation. -/
theorem retained_read (heap : Heap) (n initial extra : Nat) (positive : 0 < n) :
    (retainedHeap heap n initial extra).read (savedBuffer heap n initial) 0 = .ok initial := by
  have bound : 0 < (Array.replicate n initial : Array Nat).size := by
    simpa only [Array.size_replicate] using positive
  have loaded : (retainedHeap heap n initial extra).read (savedBuffer heap n initial) 0 =
      .ok ((Array.replicate n initial : Array Nat)[0]'bound) :=
    (retained_contents heap n initial extra).read (index := 0) bound
  simpa only [Array.getElem_replicate] using loaded

/-- Producer execution terminates for all natural inputs and every initial heap. -/
theorem make_exec (heap : Heap) (n initial : Nat) :
    Exec program (program.body makeId) ⟨makeArgs n initial, heap⟩
      ⟨makeArgs n initial, (heap.alloc (τ := .nat) n initial).2⟩
      (.returned (savedBuffer heap n initial)) :=
  .alloc (.ret _ _)

private theorem inspect_exec (heap : Heap) (n initial extra : Nat) :
    Exec program inspectBody (inspectState heap n initial extra)
      (inspectState heap n initial extra) (.returned (savedBuffer heap n initial)) := by
  refine Exec.letPrim (finish := branchState heap n initial extra) ?_
  by_cases empty : n = 0
  · exact .iteTrue
      (by simp [inspectState, Prim.eval, Atom.eval, State.cons, retainArgs, empty])
      (.ret original (branchState heap n initial extra))
  · refine .iteFalse
      (by simp [inspectState, Prim.eval, Atom.eval, State.cons, retainArgs, empty]) ?_
    exact .read (kind := .nat) (buffer := original) (index := .nat 0)
      (continuation := .ret (.var (.there (.there (.there .here)))))
      (entry := branchState heap n initial extra)
      (finish := State.cons (τ := .nat) initial (branchState heap n initial extra))
      (value := initial)
      (retained_read heap n initial extra (Nat.pos_of_ne_zero empty))
      (.ret (.var (.there (.there (.there .here))))
        (State.cons (τ := .nat) initial (branchState heap n initial extra)))

/-- The caller retains both allocations and returns the first descriptor.
The same theorem includes `n = 0`; no fake read or default cell is needed. -/
theorem retain_exec (heap : Heap) (n initial extra : Nat) :
    Exec program (program.body retainId) ⟨retainArgs n initial extra, heap⟩
      ⟨retainArgs n initial extra, retainedHeap heap n initial extra⟩
      (.returned (savedBuffer heap n initial)) :=
  .callReturn (fn := makeId) (args := producerArgs) (continuation := retainContinuation)
    (entry := ⟨retainArgs n initial extra, heap⟩)
    (calleeFinish := ⟨makeArgs n initial, (heap.alloc (τ := .nat) n initial).2⟩)
    (value := savedBuffer heap n initial)
    (finish := (inspectState heap n initial extra).tail)
    (make_exec heap n initial)
    (.alloc (kind := .nat) (length := .var (.there (.there (.there .here))))
      (initial := .nat 0) (continuation := inspectBody)
      (entry := afterCallState heap n initial extra) (finish := inspectState heap n initial extra)
      (inspect_exec heap n initial extra))

private theorem program_noCellWrites (fn : Fin signatures.length) :
    (program.body fn).NoCellWrites := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun fn => Fin.elim0 fn)) fn
  · change makeBody.NoCellWrites
    simp [makeBody]
  · change retainBody.NoCellWrites
    simp [retainBody, retainContinuation, inspectBody, returnOriginal, readOriginal]

/-- Every old view survives the complete caller execution by the shared frame
rule, without replaying its individual allocations in this proof. -/
theorem retained_frame (heap : Heap) (n initial extra : Nat)
    {kind : CellTy} {view : Buffer kind} {contents : Array (CellValue kind)}
    (observed : view.Contents heap contents) :
    view.Contents (retainedHeap heap n initial extra) contents :=
  (retain_exec heap n initial extra).contents_frame program_noCellWrites
    (program_noCellWrites retainId) observed

/-- The returned empty object remains valid and has fresh identity after the later allocation. -/
theorem retained_empty (heap : Heap) (initial extra : Nat) :
    (savedBuffer heap 0 initial).Contents (retainedHeap heap 0 initial extra) #[] ∧
      (savedBuffer heap 0 initial).object = heap.objects.size := by
  exact ⟨by simpa only [Array.replicate_zero] using retained_contents heap 0 initial extra, rfl⟩

/-- Actual return-field copying and flag assignment for the two-word result. -/
def returnSteps : Nat := 2 * fieldCount (.buffer .nat) + 2

/-- The producer pays the shared allocator's counted initialization and its return. -/
def makeSteps (n : Nat) : Nat := 14 * n + 18 + returnSteps

/-- Only the nonempty branch executes the heap read; branch prices come from
the corresponding arena cost constructors. -/
def inspectSteps (n : Nat) : Nat :=
  primCodeSize (.eq (.nat 0) (.nat 0) : Prim [] .bool) +
    if n = 0 then returnSteps + 3 else readCodeSize + returnSteps + 2

/-- The continuation's second allocation does not reuse the first allocation's capacity. -/
def continuationSteps (n extra : Nat) : Nat := 14 * extra + 18 + inspectSteps n

/-- Call overhead uses the real generated callee frame and includes its body flag initialization. -/
def retainSteps (n extra : Nat) : Nat :=
  callCost program makeId (makeSteps n + 2) + continuationSteps n extra

/-- The exact producer count observes the source execution above, with backend
range/capacity assumptions separated from its unconditional mathematical result. -/
theorem make_ready_cost (heap : Heap) (n initial : Nat) {w heapLimit depth cursor : Nat}
    (nFits : n < 2 ^ w) (initialFits : initial < 2 ^ w)
    (capacity : cursor + n ≤ heapLimit) :
    ∃ ready : ArenaReady (make_exec heap n initial) w heapLimit depth cursor (cursor + n),
      ArenaExecutionCost ready (makeSteps n) := by
  have returnedFits : ValueFits w (τ := .buffer .nat) (savedBuffer heap n initial) := nFits
  let ready : ArenaReady (make_exec heap n initial) w heapLimit depth cursor (cursor + n) :=
    .alloc (kind := .nat) (length := (.var .here : Atom [.nat, .nat] .nat))
      (initial := .var (.there .here)) (continuation := .ret (.var .here))
      (entry := ⟨makeArgs n initial, heap⟩) (finish := makeReturnState heap n initial)
      initialFits capacity (.ret (.var .here) (makeReturnState heap n initial) returnedFits)
  refine ⟨ready, ?_⟩
  exact .alloc (kind := .nat) (length := (.var .here : Atom [.nat, .nat] .nat))
    (initial := .var (.there .here)) (continuation := .ret (.var .here))
    (entry := ⟨makeArgs n initial, heap⟩) (finish := makeReturnState heap n initial)
    (initialFits := initialFits) (capacity := capacity)
    (.ret (.var .here) (makeReturnState heap n initial) (fits := returnedFits))

private theorem inspect_ready_cost (heap : Heap) (n initial extra : Nat)
    {w heapLimit depth cursor : Nat} (nFits : n < 2 ^ w) (initialFits : initial < 2 ^ w) :
    ∃ ready : ArenaReady (inspect_exec heap n initial extra)
        w heapLimit depth cursor cursor,
      ArenaExecutionCost ready (inspectSteps n) := by
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  have returnedFits : ValueFits w (τ := .buffer .nat) (savedBuffer heap n initial) := nFits
  have comparisonFits : PrimFits w (inspectState heap n initial extra).locals
      (.eq (.var (.there (.there .here))) (.nat 0)) := ⟨nFits, zeroFits⟩
  by_cases empty : n = 0
  · have test : decide (n = 0) = true := by simp [empty]
    let ready : ArenaReady (inspect_exec heap n initial extra)
        w heapLimit depth cursor cursor :=
      .letPrim comparisonFits
        (.iteTrue (condition := (.var .here : Atom BranchContext .bool))
          (entry := branchState heap n initial extra) (no := readOriginal) (test := test)
          (.ret original (branchState heap n initial extra) returnedFits))
    refine ⟨ready, ?_⟩
    simpa only [inspectSteps, if_pos empty, primCodeSize] using
      (ArenaExecutionCost.letPrim (fits := comparisonFits)
        (.iteTrue (condition := (.var .here : Atom BranchContext .bool))
          (entry := branchState heap n initial extra) (no := readOriginal) (test := test)
          (.ret original (branchState heap n initial extra) (fits := returnedFits))))
  · have test : decide (n = 0) = false := by simp [empty]
    have loaded := retained_read heap n initial extra (Nat.pos_of_ne_zero empty)
    let ready : ArenaReady (inspect_exec heap n initial extra)
        w heapLimit depth cursor cursor :=
      .letPrim comparisonFits
        (.iteFalse (condition := (.var .here : Atom BranchContext .bool))
          (entry := branchState heap n initial extra) (yes := returnOriginal) (test := test)
          (.read (kind := .nat) (buffer := original) (index := .nat 0)
            (continuation := .ret (.var (.there (.there (.there .here)))))
            (entry := branchState heap n initial extra)
            (finish := State.cons (τ := .nat) initial (branchState heap n initial extra))
            (value := initial) (loaded := loaded)
            returnedFits zeroFits initialFits
            (.ret (.var (.there (.there (.there .here))))
              (State.cons (τ := .nat) initial (branchState heap n initial extra)) returnedFits)))
    refine ⟨ready, ?_⟩
    simpa only [inspectSteps, if_neg empty, primCodeSize] using
      (ArenaExecutionCost.letPrim (fits := comparisonFits)
        (.iteFalse (condition := (.var .here : Atom BranchContext .bool))
          (entry := branchState heap n initial extra) (yes := returnOriginal) (test := test)
          (.read (kind := .nat) (buffer := original) (index := .nat 0)
            (continuation := .ret (.var (.there (.there (.there .here)))))
            (entry := branchState heap n initial extra)
            (finish := State.cons (τ := .nat) initial (branchState heap n initial extra))
            (value := initial) (loaded := loaded)
            (bufferFits := returnedFits) (indexFits := zeroFits) (valueFits := initialFits)
            (.ret (.var (.there (.there (.there .here))))
              (State.cons (τ := .nat) initial (branchState heap n initial extra))
              (fits := returnedFits)))))

/-- One true source call and both allocations share a monotonically growing cursor.
The exact call count is derived from the actual compiled function, not a chosen ABI price. -/
theorem retain_ready_cost (heap : Heap) (n initial extra : Nat)
    {w heapLimit cursor : Nat} (nFits : n < 2 ^ w) (initialFits : initial < 2 ^ w)
    (capacity : cursor + n + extra ≤ heapLimit) :
    ∃ ready : ArenaReady (retain_exec heap n initial extra)
        w heapLimit 1 cursor (cursor + n + extra),
      ArenaExecutionCost ready (retainSteps n extra) := by
  have firstCapacity : cursor + n ≤ heapLimit := by omega
  obtain ⟨calleeReady, calleeCost⟩ :=
    make_ready_cost heap n initial (depth := 0) nFits initialFits firstCapacity
  obtain ⟨inspectionReady, inspectionCost⟩ :=
    inspect_ready_cost heap n initial extra (depth := 1) (cursor := cursor + n + extra)
      nFits initialFits
  have zeroFits : 0 < 2 ^ w := Nat.two_pow_pos w
  have arguments : EnvFits w (makeArgs n initial) :=
    EnvFits.cons (τ := .nat)
      (EnvFits.cons (τ := .nat) (EnvFits.empty w) initial initialFits) n nFits
  let ready : ArenaReady (retain_exec heap n initial extra)
      w heapLimit 1 cursor (cursor + n + extra) :=
    .callReturn (fn := makeId) (args := producerArgs) (continuation := retainContinuation)
      (entry := ⟨retainArgs n initial extra, heap⟩)
      (calleeFinish := ⟨makeArgs n initial, (heap.alloc (τ := .nat) n initial).2⟩)
      (value := savedBuffer heap n initial)
      (finish := (inspectState heap n initial extra).tail)
      (fun {τ} => arguments (τ := τ)) calleeReady
      (.alloc (kind := .nat) (length := (.var (.there (.there (.there .here))) :
          Atom [.buffer .nat, .nat, .nat, .nat] .nat))
        (initial := .nat 0) (continuation := inspectBody)
        (entry := afterCallState heap n initial extra) (finish := inspectState heap n initial extra)
        zeroFits capacity inspectionReady)
  refine ⟨ready, ?_⟩
  exact .callReturn (fn := makeId) (args := producerArgs) (continuation := retainContinuation)
    (entry := ⟨retainArgs n initial extra, heap⟩)
    (calleeFinish := ⟨makeArgs n initial, (heap.alloc (τ := .nat) n initial).2⟩)
    (value := savedBuffer heap n initial) (finish := (inspectState heap n initial extra).tail)
    (arguments := fun {τ} => arguments (τ := τ)) calleeCost
    (.alloc (kind := .nat) (length := (.var (.there (.there (.there .here))) :
        Atom [.buffer .nat, .nat, .nat, .nat] .nat))
      (initial := .nat 0) (continuation := inspectBody)
      (entry := afterCallState heap n initial extra) (finish := inspectState heap n initial extra)
      (initialFits := zeroFits) (capacity := capacity) inspectionCost)

set_option maxRecDepth 2048 in
/-- The actual compiled caller halts with the first array still represented
after both allocations. The same final target witnesses the exact runner count,
returned descriptor, extended placement and cumulative arena extent.
The two-frame stack bound covers this caller and its real producer call. -/
theorem retain_runUntil (heap : Heap) (n initial extra : Nat)
    {w heapLimit cursor : Nat} (hw : 0 < w) (initialFits : initial < 2 ^ w)
    (entry : Ram.Source.State w) {placement : Nat → Ram.Word w}
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (capacity : cursor + n + extra ≤ heapLimit)
    (codeCapacity : (lowerCode program retainId).length < 2 ^ w)
    (stackCapacity : heapLimit + 2 * Ram.ABI.frameSize (programControl program) < 2 ^ w) :
    ∃ finalPlacement finishTarget target,
      Ram.Source.FunctionMeasuredExec (programControl program) (lowerProgram program) heapLimit 1
        (lowerFunc program retainId) (envWords placement (retainArgs n initial extra))
        (retainSteps n extra + 2) entry
        (valueWords finalPlacement (τ := .buffer .nat) (savedBuffer heap n initial)) finishTarget ∧
      ArenaRep finalPlacement (cursor + n + extra) heapLimit
        (retainedHeap heap n initial extra) finishTarget ∧
      Placement.Agrees heap placement finalPlacement ∧
      Ram.LocalCompiler.Function.runUntil (programControl program) (lowerProgram program)
          retainId.val (contextSize signatures[retainId].params) heapLimit
          (envWords placement (retainArgs n initial extra)) entry =
        some ⟨target, Ram.LocalCompiler.Function.callSteps (programControl program)
          (lowerFunc program retainId) (retainSteps n extra + 2) + 1, .halted⟩ ∧
      Ram.LocalCompiler.Function.returnedValues (fieldCount signatures[retainId].result) target =
        valueWords finalPlacement (τ := .buffer .nat) (savedBuffer heap n initial) ∧
      (bufferRef finalPlacement (savedBuffer heap n initial)).Rep heapLimit
        (objectWords w (τ := .nat) (Array.replicate n initial)).toList finishTarget ∧
      Ram.Source.State.Observes heapLimit 0 finishTarget target := by
  have wordLimit := arena.limit_lt
  have nFits : n < 2 ^ w := by omega
  have extraFits : extra < 2 ^ w := by omega
  obtain ⟨ready, cost⟩ := retain_ready_cost heap n initial extra nFits initialFits capacity
  have arguments : EnvFits w (retainArgs n initial extra) :=
    EnvFits.cons (τ := .nat)
      (EnvFits.cons (τ := .nat)
        (EnvFits.cons (τ := .nat) (EnvFits.empty w) extra extraFits) initial initialFits) n nFits
  have rooted : (retainArgs n initial extra).Rooted heap :=
    Env.Rooted.cons (τ := .nat)
      (Env.Rooted.cons (τ := .nat)
        (Env.Rooted.cons (τ := .nat) (Env.Rooted.empty heap) extra trivial)
          initial trivial) n trivial
  obtain ⟨finalPlacement, finishTarget, target, invocation, finalArena, agreed,
    returned, fields, observed⟩ :=
    cost.runUntil (fn := retainId) hw arguments rooted entry arena codeCapacity stackCapacity
  exact ⟨finalPlacement, finishTarget, target, invocation, finalArena, agreed,
    returned, fields, finalArena.heapRep.view (retained_contents heap n initial extra) nFits,
    observed⟩

end Complexity.Language.Examples.Allocation
