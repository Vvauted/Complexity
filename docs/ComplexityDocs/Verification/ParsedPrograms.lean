/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Parsed
import Complexity.Computability.Ram.Compiler.Language.Program.Parsed

/-!
# Programs over input and output sequences

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

A program's external format need not be the mathematical structure used to state
its specification. For example, a program can receive a sequence of numerical
input tokens while its postcondition concerns a graph described by that sequence.
The implementation may scan the tokens directly or construct its own data
structures. It need not materialize the specification's graph record or lists.

## Keep the original mathematical statement

Fix input and output parsers as part of the interface, independently of the
implementation. For a program from raw inputs to raw outputs,
`program.CorrectParsed parseInput parseOutput valid post` says:

- whenever the raw input parses to a legal mathematical input,
- the actual program terminates successfully on that raw input,
- its actual output parses to an answer satisfying the original postcondition.

This is the existing total-correctness interface on raw values:
`correctParsed_iff_correct` states the equivalence. No second evaluator or
runtime parser primitive is introduced. The mathematical parser is not a free
callback available to the implementation, and its decoded object is not added
to the initial heap.

The interface author must show that the format covers every intended instance.
One standard argument supplies a fixed encoder and proves that parsing its
result returns each legal input. `CorrectParsed.on_encoded` then obtains an
actual successful output for that instance. Without such coverage, a parser
that rejects all inputs would make correctness vacuous. The output parser
should describe the required external answer format, not repair a candidate's
answer or compute the solution on its behalf.

## Charge the same computation

`program.TimeOParsed parseInput valid growth` applies the existing
`TimeOOn` interface to accepted raw inputs, using the mathematical input to
state the growth expression. Actual reads, runtime parsing, working allocations
and output construction remain instructions of the selected program. A source
that constructs the mathematical representation must pay for that construction;
a source using another representation need not construct it at all.

Correctness remains independent of a time budget. `TimeOParsed.runs_correct`
combines the two proofs into a bound and decoded postcondition for the same
actual RAM execution, at every admitted word width. Admission uses the fixed raw
input representation, not extra decoded objects or candidate-selected advice.
The mathematical size expression affects the theorem, not runtime inputs.

## State the input boundary

Numerical word tokens and decimal text bytes are different interfaces. At a
word-token boundary, whitespace handling and decimal conversion by an external
driver are outside the program. At a byte-text boundary, the source must perform
and pay for the required text parsing. Likewise, returning output tokens does
not itself account for an external printer's decimal formatting or transport.
These modules do not supply a streaming driver or an executable I/O adapter.

For interaction, expose only the current request and retain the actual state
between calls. A specification may observe a full history, but supplying future
requests or hidden feedback as a raw initial sequence would change the problem.
Use the [session interface](ComplexityDocs/Verification/Sessions.html) for that
causal boundary.
-/
