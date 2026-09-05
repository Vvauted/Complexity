# Function and recursive-call compilation protocol

Status: implemented and individually checked on 0v0 with Lean 4.28.0-rc1.
`ABI`, `Arguments`, `Frame`, `CallSetup`, and `CallReturn` implement the concrete
protocol. `Compiler`, `Structural`, `Call`, and `Program` prove linked execution
including recursion; `Exact` and `simulate_call_exact` retain exact step counts.
The whole-program functional theorem no longer has an unresolved call-simulation
premise. `Measured` retains exact counts, `Contracts` provides budget proofs, and
the larger array-sum and recursive-factorial examples use the resulting compiler.

The protocol uses the existing word-RAM only. A save, restore, argument copy,
or address calculation is an actual sequence of its instructions, never a
primitive that copies an entire frame or runs an arbitrary Lean callback.

## Static register layout

Choose one natural `N` for the complete fixed program, including its entry
statement, such that every function satisfies `params ≤ locals ≤ N` and every
source register access is within that function's declared locals. Check function
lookup and arity statically before linking. These are compiler well-formedness
conditions; this protocol does not insert implicit runtime bounds checks.

| Physical register | Use |
| --- | --- |
| `i`, where `i < N` | Source local `i` |
| `SP = N` | Next free stack address |
| `RV = N + 1` | Returned word |
| `RA = N + 2` | Return code address |
| `ADDR = N + 3` | Stack-address temporary |
| `TMP = N + 4` | Stack-offset or immediate temporary |
| `ARG(i) = N + 5 + i`, where `i < N` | Evaluated argument buffer |
| `scratch = 2*N + 5` and above | Expression compiler temporaries |

Compile every expression using `Expr.compile e scratch`. Source variables remain
the same physical registers: no renaming is required. All ABI registers and
argument buffers are strictly below `scratch`, so
`Expr.compile_correct.below` protects them during expression evaluation.
`Source.State.Matches.compile_expr` accepts `locals ≤ scratch` and supplies the
corresponding value and source-visible state relation when target memory also
contains a private stack. Call setup may overwrite the ABI temporaries, but not
the source locals or the argument buffer until its respective phase permits it.

The finite program determines `N` and all referenced register names. A recursive
call reuses this register layout; it does not allocate new physical register
names or expand another copy of the function's code.

## Memory partition and frame layout

Let `H` be the source-visible heap boundary. Source memory accesses must use
word addresses whose decoded values are below `H`. The stack grows upward from
`H`. If the entry SP of a call is `b`, its frame has `F = N + 1` words:

```text
address b         : return code address
address b + 1 + i : caller local i, for 0 ≤ i < N
next free address : b + F
```

Use the relation already defined in `Ram/Memory.lean`:

```lean
HeapEqBelow H source.mem target.mem
Source.State.Matches H N source target
```

Do not require `source.mem = target.mem`. Compiler-owned stack words differ from
the source heap function, and popped frames may leave stale words behind.
Only source locals below `N`, heap below `H`, input, output, and running status
are related by `Matches`. Transferring a postcondition to the target must respect
this observation boundary; arbitrary observations of inaccessible source heap
words or registers outside the local bound are not justified by `Matches`.

`HeapEqBelow.setMem_above` is the existing fact that a compiler stack write
preserves source-heap agreement. Existing `Expr.ReadsBelow`,
`Expr.eval_eq_of_readsBelow`, and `Matches.compile_expr` handle source expressions
without falsely equating the whole source and target memories.

## Call-site code

For `.call dst fn args`, let `p = args.length = callee.params`, let `entry(fn)`
be the linked function entry, and let `returnPC` point to the final move below.
All displayed instructions are existing `Instr` constructors. Compile-time
iteration over `i` emits individual instructions; it is not a runtime primitive.

1. Evaluate and buffer all arguments in caller state, in list order:

   ```text
   for i = 0, ..., p-1, emit:
     args[i].compile scratch
     move ARG(i) scratch
   ```

   Source expressions are pure. Every expression preserves source locals, all
   memory, and all previously buffered arguments. Do not overwrite source
   parameter registers while there are still caller arguments to evaluate.

2. Save the return address and every caller local:

   ```text
   const TMP returnPC
   store SP TMP
   for i = 0, ..., N-1, emit:
     const TMP (i + 1)
     binop add ADDR SP TMP
     store ADDR i
   ```

3. Install the callee's local state:

   ```text
   for i = 0, ..., p-1, emit:
     move i ARG(i)
   for i = p, ..., N-1, emit:
     const i 0
   ```

   This agrees with `Source.State.enter` on every source-observable register.
   Argument buffers are distinct from all source locals, so copying one
   parameter cannot destroy a later parameter. Buffers need not survive the
   call after the callee locals have been initialized.

4. Advance the stack and enter the function:

   ```text
   const TMP F
   binop add SP SP TMP
   jump entry(fn)
   ```

5. At `returnPC`, receive the result before the caller's continuation:

   ```text
   move dst RV
   ```

## Function body and return code

The callee body executes with SP equal to `b + F`. Its statement-compilation
theorem must preserve that SP and all older stack words. After the body completes
normally, evaluate `callee.result` and return:

```text
callee.result.compile scratch
move RV scratch
const TMP F
binop sub SP SP TMP
load RA SP
for i = 0, ..., N-1, emit:
  const TMP (i + 1)
  binop add ADDR SP TMP
  load i ADDR
jumpReg RA
```

The result is evaluated before caller locals are restored, as required by
`Source.State.leave`. `RV`, `RA`, `SP`, `ADDR`, and `TMP` are not source locals;
restoring a local cannot overwrite them. After the indirect jump, the call-site
`move dst RV` changes exactly the returned destination in the restored caller.
The callee's heap and input/output effects are retained.

## Resource and execution-safety obligations

`Source.SafeExec` is the indexed safe-execution judgment, with an erasure theorem
to `Source.Exec`. `Source.MeasuredExec` further retains compiler-derived counts.
Neither is a user-supplied cost table or a replacement for source behavior.
Their safety cases are:

- Assignment/write/condition: the evaluated expression satisfies `ReadsBelow H`.
- Store: both expressions satisfy `ReadsBelow H`, and the evaluated destination
  address is below `H`.
- Sequence and loop: safety holds at the actual intermediate source states;
  the same remaining nested-call bound is available to each sequential segment.
- Call: each argument satisfies `ReadsBelow H` in the original caller; the
  callee body satisfies safety with one fewer available nested call; the result
  expression satisfies `ReadsBelow H` in the final callee state.
- Read: retain the existing successful-read premise; exhausted input is not
  silently turned into a successful source run.

For an entry SP represented by natural `b` and remaining nested-call bound `d`,
use the sufficient arithmetic conditions

```text
0 < w
H ≤ b
b + d*F < 2^w
```

The strict last inequality ensures that even the exclusive-end SP is itself a
representable word. At a call, require `d > 0`; the child resource condition is
`(b+F) + (d-1)*F < 2^w`. Prove that encoding offsets and adding/subtracting the
frame size agree with natural stack-address arithmetic under these hypotheses.
No stack access may rely on modular wraparound accidentally reaching the desired
cell. These conditions do not prohibit ordinary source modular arithmetic.

Return addresses must encode exactly into words. A simple sufficient linker
condition is `code.length < 2^w`, together with membership of every resolved
entry and return label in the code. Code is fixed before quantifying over inputs
and admissible word widths; labels must not depend on runtime data or recursion
depth. Missing labels and invalid arities must be rejected, not assigned a
default code address.

Heap-safety and stack-resource obligations are necessary because this ISA has
one memory space and no hardware access protection. Source programs that read
or write the reserved stack are outside this compiler-correctness theorem, not
evidence that the unrestricted source and target heaps are globally equal.

## Induction contract for the compiler proof

For a statement starting at target SP `b`, the simulation theorem should return
an actual target execution `Ram.Exec code steps start finish` and establish:

- `Source.State.Matches H N sourceFinal finish`.
- The specified linked continuation PC and running status.
- The final SP equals the initial SP.
- For every word address `a` with `H ≤ a.toNat < b`,
  `finish.mem a = start.mem a`.

The final condition is a small frame rule; a separate inductive list of stack
objects is not needed for the first proof. When applying the callee-body
induction hypothesis with entry SP `b+F`, this condition protects both earlier
frames and the new saved frame `[b,b+F)`. Return code can therefore reload the
saved return address and every caller local. On returning to the caller, only
preservation below `b` is promised; stale data in the popped frame is irrelevant.

The proofs use finite execution derivations, not an acyclic call graph.
`Program` closes call simulation by strong induction on the available call depth;
`Measured` uses induction on the measured execution. The call constructor has a
smaller body derivation even for self-recursion or mutual recursion. The linker
places all function bodies once in a shared code list, computes block lengths
without following calls, and then resolves labels. Label values do not change
emitted instruction counts.

## Machine-step accounting

Use `CodeAt`, `execBlock_exec`, `Exec.single`, and `Exec.trans` to prove the
generated setup, save, restore, jump, and receive sequences actually execute.
Nonlinear jump instructions are individual machine transitions, not part of a
purported linear `execBlock` proof. Compose these with the compiled callee body
and result-expression executions.

For exactly the implemented sequences displayed here, `ABI.call_steps_eq` in
`CodeLength.lean` proves the identity

```text
sum of compiled argument lengths
+ actual compiled callee-body steps
+ compiled result length
+ 7*N + p + 11
```

The formula is derived from the lengths of the generated instruction lists.
`Compiler.simulate_call_exact` proves execution of those blocks, including the
entry jump, actual body, return jump, and receive instruction. Thus the formula
can simplify a proved machine count; it does not define call cost separately.
Changing emitted code requires proving the corresponding length identities and
execution theorem again. No source constructor accepts a price from its author.

`Compiler.compileChecked_runs` establishes a successful full run with matching
output and remaining input. The fixed linked code is shared by every recursive
invocation; call-depth bounds control stack capacity, not instruction counts.
`Measured` and `Contracts` connect high-level budget proofs to these exact
executions. `Examples/Factorial` exercises ordinary recursion through this ABI,
including a proved nonconstant complete-program transition count.
