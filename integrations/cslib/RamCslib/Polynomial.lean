/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity.Polynomial
import Ram.Problem

/-!
# Compatibility import for polynomial complexity

The public polynomial growth API uses mathlib directly in
`Ram.Complexity.Polynomial`; fixed-problem asymptotic certificate constructors
are in `Ram.Problem`. This import path reexports those declarations for clients
of the optional CSLib integration. It defines no second asymptotic relation.
-/
