# Literature and architectural choices

This document records the primary sources behind the design in
[DESIGN.md](DESIGN.md). They motivate the architecture; they do not certify our
implementation. The completion obligations remain proofs about this repository's
source language, compiler, and fixed target machine. Published results about a
different language or cost model are not substitutes for that connection.

## 1. RAM is a specified model, not a cost-free abstraction

Stephen A. Cook and Robert A. Reckhow, **Time Bounded Random Access Machines**,
JCSS 7, 1973, pp. 354–375.
[Author-hosted paper](https://www.cs.utoronto.ca/~sacook/homepage/rams.pdf).

Sections 1–2 define a finite program operating on unbounded integer registers,
with instruction costs governed by a number-length function. The paper considers
constant and logarithmic length costs. Its primitive arithmetic includes addition
and subtraction, but not multiplication. RAM-ALGOL supplies a structured language
and a translation whose cost can be related to the source program. However,
RAM-ALGOL excludes recursive procedures and uses one-dimensional infinite arrays;
its procedure expansion is not a solution for our recursive language.

Our choice differs deliberately: words have bounded, explicit bit-vector
semantics, and multiplication belongs to the fixed target instruction vocabulary.
We must not cite Cook–Reckhow as establishing constant-time multiplication in its
original machine. The relevant lesson is to fix the computational model and prove
the source/target relationship, including addressing and storage conventions.

## 2. Word arithmetic and the instruction vocabulary matter

Torben Hagerup, **Sorting and Searching on the Word RAM**, STACS 1998,
pp. 366–398.
[Publisher page](https://link.springer.com/chapter/10.1007/BFb0028575).

The publicly accessible abstract characterizes a word-RAM as a unit-cost RAM
with words of width `w` and a computer-like instruction repertoire. It also
emphasizes that comparison-based lower bounds for sorting and searching need not
hold on this model. Only that abstract, not the subscription chapter's complete
model definition, was checked for this document.

Accordingly, our exact instruction set must be documented in our own semantics,
not inferred from the name "word-RAM". A multiplication instruction computes a
word result; a theorem connects that result to mathematical multiplication modulo
`2^w`, and another recovers exact multiplication under a no-overflow hypothesis.
Neither theorem turns arbitrary-precision multiplication into one instruction.
The benchmark must constrain admissible word widths and quantify a fixed program
uniformly over inputs, rather than allowing input-dependent instruction sets.

## 3. Derive source costs from the compilation chain

Roberto M. Amadio and Yann Régis-Gianas, **Certifying and reasoning about cost
annotations of functional programs**.
[Author-deposited paper](https://arxiv.org/abs/1110.2350).

This work develops a labelling method that connects cost annotations on
higher-order source programs to compiled execution. Labels are preserved through
compilation transformations, allowing target-level cost information to be used
when reasoning about source programs. It addresses closure conversion and safe
region-based memory management as well as functional compilation. The treatment
of regions explicitly discusses allocation and disposal; it does not justify
arbitrary bulk memory operations being free.

For us, the important direction is target-to-source: define target execution
first, prove compilation preserves results and control flow, and derive cost
rules from the resulting executions. We do not need to reproduce this compiler
pipeline or claim that its backend discussion is a machine-checked Lean result.
Our first-order calling convention still requires actual machine operations for
arguments, saved state, frame access, and return. A cost theorem for expressions
alone cannot establish those obligations.

## 4. Use time credits as proof resources, not cost definitions

Arthur Charguéraud and François Pottier, **Verifying the Correctness and Amortized
Complexity of a Union-Find Implementation in Separation Logic with Time Credits**,
JAR, 2017.
[Author-hosted paper](https://www.chargueraud.org/research/2017/credits_jar/credits_jar.pdf).

The paper combines mutable-memory assertions with time credits, allowing modular
correctness and amortized-cost specifications for union-find. Potential can be
stored within an abstract data-structure assertion, so client proofs need not
expose its representation. This is useful guidance for arrays, recursive
functions, and data-structure contracts.

The boundaries matter: Section 2.7 counts source function calls and explicitly
does not verify the OCaml compiler's complexity preservation. Section 2.2 also
discusses the gap between ideal integers in proofs and overflowing machine
integers. We should adopt neither gap. Our credits, if introduced, must be sound
against counted RAM transitions, and our arithmetic lemmas must respect actual
word semantics. A user may propose a budget or potential and prove it sufficient;
that is not permission to define an operation's execution cost.

Section 4 is also a useful guide to proof ergonomics. Its syntax-directed
characteristic formulae leave recursive proofs to the host prover's ordinary
induction. Type-directed lifting lets postconditions use mathematical values
instead of repeatedly classifying raw runtime values. For us this motivates
declaration-generated binding equations and shared exact-cost composition,
not a second recursive proof framework. We retain proved RAM primitive and
calling costs rather than importing its function-call counting convention;
abstract interfaces must be backed by our existing execution theorems.

More specifically, Section 4.1's `let` rule passes the intermediate value to a
continuation. Our single-assignment `TotalWP.assign_value` uses that proof shape
on the existing deterministic source semantics: it retains an evaluation equality
while the search proof reasons about a named midpoint. This is a small local
application, not generated characteristic formulae for the whole language or a
port of the paper's separation logic. The actual assignment remains charged.

The introduction also points out a modularity cost of exposing exact numerical
constants in client specifications: implementation changes can force client
proof changes. We should retain concrete transition theorems for executable
accounting while allowing mathematical clients to use derived mathlib `IsBigO`
statements. Hiding constants must not hide the input domain, word-width policy
or an unproved representation cost. This does not require a second asymptotics
library or weakening the counted execution theorem.

Section 3.3 makes budget splitting concrete: a caller with `m` credits can
provide `n` to a callee and retain `m - n`, provided `n ≤ m`. It also explicitly
distinguishes this accounting algebra from its connection to measured execution.
For our separate time rules, this motivates deriving the continuation reserve
from the current bound and an already proved compiled-call bound. Affordability
must remain a proof obligation; natural-number subtraction alone cannot justify
overspending. This is an application of our existing call theorem, not a new
heap-credit semantics or a change to budget-free functional correctness.

## 5. Separate algorithmic reasoning from representation proofs

Maximilian P. L. Haslbeck and Peter Lammich, **Refinement with Time — Refining the
Run-Time of Algorithms in Isabelle/HOL**, ITP 2019.
[Published paper and PDF](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.20).

Timed refinement connects abstract algorithm specifications to executable
Imperative/HOL programs while preserving functional results and time bounds.
The development includes recursion, loops, verification-condition generation, and
composable data-structure refinements, illustrated by Kruskal and Edmonds–Karp.

Its concrete cost layer is still an abstraction: Section 3.1 assigns unit cost to
many basic commands and `n+1` to whole-array operations. That is not itself a proof
about our fixed RAM instructions. We can reuse the architectural idea while
requiring our library contracts to terminate in proved implementations. Array
initialization must execute the corresponding stores; array access needs address
and representation lemmas. Clients should use those proved contracts without
reopening the compiler.

Section 3.2 makes a further useful distinction: a bind carries both the result
relation and the updated relations for live data into its continuation. Section
4.2 separates structural automation from proving operation side conditions.
For our merge-sort migration, this points to reusing the existing two-buffer
split/reassembly proofs independently of parameter slots and return fields.
The real caller should receive the changed array representations and frame;
sortedness, containment and aliasing premises remain mathematical obligations.
This motivates improving our existing call rules, not porting Sepref or treating
an abstract operation as an uncharged RAM instruction.

The same Section 4.2 distinction guides general loop-body support: a structural
rule should handle iteration mechanics while concrete operation contracts retain
their side conditions. Our `forIn` rules therefore separate real loads and cursor
updates from the arbitrary body invariant, and keep a conditional time theorem
independent of body totality. Existing scalar-fold conveniences remain useful;
making their clients repeat a general invariant would not itself improve the
proof experience. This is our application of the methodology, not a claim to
have implemented Sepref's synthesis or its different cost model.

## 6. Separate behavior and cost without changing the machine

Yue Niu, Jonathan Sterling, Harrison Grodin and Robert Harper,
**A cost-aware logical framework**, POPL 2022.
[Author-deposited paper](https://arxiv.org/abs/2107.04663) and
[official Agda implementation](https://github.com/calfproject/agda-calf).

Sections 2.1–2.7 distinguish values from computations, behavioral equality from
cost-sensitive reasoning, and establish internal noninterference: behavior
cannot inspect cost. Section 1.6 discusses both accessibility predicates and
cost clocks for recursion. Its abstract cost semantics is not a simulation of
our word-RAM.

Our design takes the separation and compositionality seriously without porting
the modal type theory. `TotalWP` supplies budget-free termination and behavior;
the measured semantics must erase to the same execution, and the source must
not inspect its count. Typed arguments, returned values and effects should drive
both proof views. Behavioral equality alone must never transport a cost bound.
For recursion we retain independent termination proofs rather than requiring a
cost clock to publish correctness. Target adequacy remains the compiler's job.

The sample review gives concrete uses: factorial exposes its cost recurrence
without a second register-level induction, and typed calls compose results and
costs without unpacking execution trees. Separate theorem files alone do not
establish CALF's full phase discipline or noninterference metatheorem; those
claims are not made here.

Section 6's sorting results use a comparison-cost model, not total RAM
transitions. Our recursive sorting consumer gives a concrete instance of the
distinction: its correctness may identify the result with mathlib's canonical
`List.insertionSort`, while its cost theorem must concern the actual merge-sort
declaration, including descriptor setup, calls and copy-back. Neither a slow
reference function in a mathematical specification nor equality of sorted
results changes the implementation's complexity. No parallel-span claim is
inherited from CALF's separate parallel cost model.

Appendix A distinguishes importing host-language data and mathematics from
charging all traversals in a uniform cost model. Its imported natural-number
operations suit an algorithm-specific instrumentation, whereas its queue analysis
needs a cost-aware list type. For us, this reinforces two separate obligations:
reuse Lean and mathlib for specifications and ordinary mathematics, but justify
the cost of the actual representation and operations. In particular, a proof
that fresh local assignments preserve an existing mathematical view does not
erase those assignments from the executable program or its time theorem.

## 7. Preserve effects when composing cost arguments

Harrison Grodin, Yue Niu, Jonathan Sterling and Robert Harper,
**Decalf: A Directed, Effectful Cost-Aware Logical Framework**, POPL 2024.
[Author-deposited paper, revised version](https://arxiv.org/html/2307.05938v4).

Sections 1.3–1.5 extend the behavioral/cost distinction with directed comparisons
of effectful programs. A randomized computation need not have a pure recurrence
that exactly separates its behavior from its cost. Cost inequalities retain the
behavior of the programs being compared.

Our current RAM is deterministic, so this is not a reason to add probabilistic
semantics or a new effect framework. It is a useful design check: bounds for a
continuation must use the actual returned value and updated state. In
copy-then-sum, the copy postcondition establishes the data on which sum runs.
Generalizing the fold-cost rule should similarly retain the prefix accumulator
and represented heap, rather than require every helper to have constant cost.
Any future program-level cost refinement needs its own proof against this
repository's execution, not merely a new preorder bearing Decalf's name.

Section 3.3's `map` example sharpens this point: unknown order-dependent effects
prevent replacing a traversal by just a pure result and a length-based price.
Our current helper-call fold is deliberately read-only, scalar-accumulator and
statically linked; it is not arbitrary higher-order compilation. Its varying
cost rule retains the actual prefix accumulator. A future mutable traversal must
also propagate the changed representation in execution order. Standard `List`
identities can simplify the mathematical result, but cannot alone justify
reordering calls or transporting their costs.

Rechecking Example 3.4 for in-place map gives a concrete boundary: its concise
linear bound assumes a pure behavioral helper with a uniform cost bound; the
uninstrumented map itself carries no traversal charge in that example. Our
application is a forward, statically linked traversal whose real loads, stores,
index updates and calls are charged. Its correctness contract preserves helper
shared state and proves the unread suffix remains valid. We do not inherit the
paper's higher-order language or identify its instrumented cost with RAM steps.

## Reading discipline

Use the roadmap's current sample bottleneck to select a small part of a primary
paper. Record the useful rule or distinction, its assumptions, and the concrete
consumer it improves. Check the cited computational model before transferring a
cost claim. Revisit a decision when a sample contradicts it; do not expand the
bibliography or recreate a type theory as a substitute for a usable public rule.

## Consequences for this library

One machine transition contributes one step. Source syntax cannot accept a cost
table, an unchecked tick, or an arbitrary host-language computation. Bounds and
invariants live in proofs. The necessary chain is source behavior, compiled
behavior, counted target execution, and compositional proof rules. Termination
belongs in the certificate: a conditional bound on a nonexistent execution is
insufficient. Interpreter wall-clock time is a separate quantity, not the RAM
complexity being certified.
