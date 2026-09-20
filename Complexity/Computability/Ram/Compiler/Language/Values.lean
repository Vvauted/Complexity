/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Values.Copy
import Complexity.Computability.Ram.Compiler.Language.Values.Buffer

/-!
# Executing lowered values and bindings

This module collects the value-lowering correspondence. `Values.Basic` relates
field expressions to source values; `Values.Copy` proves sequential copies,
local bindings, assignments and returns; `Values.Buffer` connects borrowed-buffer
reads, writes and slices to the same shared heap.

All rules describe the emitted code and actual source operands. Unit has no
fictitious field or assignment, and no operation receives an unchecked cost.
-/
