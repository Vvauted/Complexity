/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Basic
import Complexity.Language.Eval.Attributes

/-!
# Simplifying native source-action equations

The dedicated `source_eval` simp set normalizes the existing exception, state
and partial-value operations, and exposes the actual buffer accesses. An author
can open one generated function equation and compose supplied access and callee
equations with `simp [source_eval, read, written, recursive, ...]`.

The set contains no source-program bodies or recursive function equations.
Calls stay opaque until their actual execution equations are supplied. It
preserves failures and actual intermediate heaps, and does not change the
global simp set, define another evaluator or assign execution costs.
-/

namespace Complexity.Language

attribute [source_eval] ExceptT.bind ExceptT.bindCont ExceptT.pure ExceptT.mk
  Bind.bind Pure.pure StateT.bind StateT.pure Part.bind_some
  Buffer.allocM Buffer.readM Buffer.writeM Buffer.sliceM

end Complexity.Language
