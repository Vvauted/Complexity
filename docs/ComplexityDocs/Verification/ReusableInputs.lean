/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session.TimeSpace
import Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareReuseBounds

/-!
# Reusable current inputs

A persistent session should not have to retain a fresh input allocation for
every request. Import `Complexity.Language.Buffer.PrepareReuse` for a reusable
natural-number buffer, and
`Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareReuseBounds`
for its actual RAM preparation and space bounds.

The protocol, not the candidate, fixes this loader. It retains an
`Option (Buffer .nat)` cache initialized to `none`. A fitting request overwrites
the cached allocation's prefix; a larger request allocates the larger of its
length and twice the previous capacity. The returned view exposes exactly the
current request length. No future request or maximum length chooses the cache.

## Contents and ownership

`PrepareReuse.Run.observed` proves the actual current contents, next-cache
validity, preservation of old object shapes, and a frame outside the borrowed
view. The input view is deliberately borrowed: later loading can change its
contents. A candidate that needs an earlier input must preserve it explicitly.
It cannot assume the old fresh-loader theorem that all previous contents stay
unchanged.

Candidate-owned allocations and persistent state are retained. The loader does
not rewind the whole heap, discard newly allocated callback state, select an
arbitrary candidate object, or pretend to free replaced buffers. Candidate code
can use the existing scoped storage interfaces for its own temporary work.

A reply's proof observation uses its return-time heap. Later overwriting of a
reused output buffer therefore does not change the earlier mathematical reply.
These heap witnesses are not runtime copies; a claim about persistent contents
still requires an appropriate ownership or frame proof.

## The same source and RAM history

`Session.StatefulPreparedRuns` threads an explicit loader cache alongside the
actual candidate state and heap. Each callback still receives only its declared
current arguments, not the loader's cache or future requests. The initial cache
is fixed by the interface. It is not reselected existentially on each call.

`StatefulPreparedSpaceRuns` records actual loader and callback executions.
Source projection preserves the exact cache sequence, candidate states,
return-time heaps and replies. Initialization is counted once, and the seeded
address footprint is retained across every call. Neither callback boundaries
nor a changed cache reset the space history.

Import `Complexity.Language.Session.TimeSpace` for joint resource contracts:
`StatefulPreparedTraceTimeSpaceOOn`, `StatefulPreparedHistoryTimeSpaceOOn`,
and the uniform or fixed-budget `StatefulPreparedWorstCaseTimeSpace` variants.
The last variants quantify over every accepted source history; they need
independent source correctness to establish an accepted successful history.
A generic preparation relation is not sufficient evidence of a concrete
loader's cost: use the checked buffer preparation and its source projection.

## What the space theorem establishes

The pure arithmetic module `Complexity.Analysis.Amortized.Geometric` proves
that, starting with zero capacity, the sum of all newly reserved buffer cells is
at most four times the largest request so far. Replaced buffers are included
in that sum; no reclamation hypothesis is hidden in the bound.

`PrepareReuse.exists_space_le_geometric` connects these actual capacity
transitions and cursor increments to the RAM loader's physical footprint.
It uses a small heap-region certificate while keeping the real stack base and
complete returned machine state. Loads and stores lie in that heap prefix or
the separate loader stack interval; the unused address gap is not charged.
Repeated calls reuse the same physical stack region.

This theorem retains explicit candidate-reservation, arena readiness, word-range,
capacity and previous-footprint premises. It does not infer a candidate's
workspace, equate a final cursor with a whole-execution peak, or make arbitrary
callback allocations free. Such helper premises must be proved on every legal
input when publishing a total resource contract.

The metric remains the library's actual seeded physical-word footprint, not
native process RSS or exact reachable-live memory. Transport and traversal of
external inputs remain outside these preloaded invocations; allocation,
initialization and each compiled scalar write are charged. General linked-list
recycling and automatic output lifetimes are not provided by this Nat-buffer
loader.
-/
