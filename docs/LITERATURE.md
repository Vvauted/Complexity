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

## 6. Separate behavior and cost without changing the machine

Yue Niu, Jonathan Sterling, Harrison Grodin and Robert Harper,
**A cost-aware logical framework**, POPL 2022.
[Author-deposited paper](https://arxiv.org/abs/2107.04663) and
[official Agda implementation](https://github.com/calfproject/agda-calf).

CALF distinguishes extensional behavior from intensional cost within a
dependent type theory. Its internal noninterference property prevents a
program's input/output behavior from depending on cost. The framework supports
ordinary mathematical libraries, recurrence reasoning and potential-based
amortized analysis. Its cost operations are an abstract cost semantics, not
by themselves a simulation theorem for our particular RAM instruction set.

Our interface adopts the separation principle: `TotalWP` and `TotalSpec`
establish safe terminating behavior without time fuel, and `TimeBound`
separately bounds compiler-derived execution counts. Their combination proves
the existing total costed contract. `Refines` connects the behavior to ordinary
Lean functions and mathlib properties through representation relations.
This is not an implementation of CALF's modal type theory, nor a claim to have
formalized its internal noninterference metatheorem. No CALF dependency or
abstract tick primitive is added; target adequacy remains our compiler proof.

## Consequences for this library

One machine transition contributes one step. Source syntax cannot accept a cost
table, an unchecked tick, or an arbitrary host-language computation. Bounds and
invariants live in proofs. The necessary chain is source behavior, compiled
behavior, counted target execution, and compositional proof rules. Termination
belongs in the certificate: a conditional bound on a nonexistent execution is
insufficient. Interpreter wall-clock time is a separate quantity, not the RAM
complexity being certified.
