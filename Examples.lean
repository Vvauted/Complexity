/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Allocation
import Examples.Language.Buffer
import Examples.Language.BufferCompiled
import Examples.Language.Factorial
import Examples.Language.FactorialCompiled
import Examples.Language.Imports
import Examples.Language.ImportsCompiled
import Examples.Language.ImportsTraversalCompiled
import Examples.Language.Linking
import Examples.Language.LinkedList
import Examples.Language.LinkedListAllocation
import Examples.Language.LinkedListCompiled
import Examples.Language.LinkedListComposition
import Examples.Language.LinkedListFoldAllocation
import Examples.Language.LinkedListViewsCompiled
import Examples.Language.OptionalBuffer
import Examples.Language.OptionalBufferCompiled
import Examples.Language.Remainder
import Examples.Language.Scalar
import Examples.Language.ScalarCompiled
import Examples.Language.Scope
import Examples.Language.ScopeCompiled
import Examples.Language.ScopeCompiledWork
import Examples.Language.Splay.Amortized
import Examples.Language.Splay.Compiled
import Examples.Language.Splay.Correctness
import Examples.Language.Splay.Cost
import Examples.Language.Splay.Sequence
import Examples.Language.Traversal
import Examples.Language.TraversalCompiled
import Examples.Language.TraversalComposition
import Examples.Language.TraversalCompositionCompiled
import Examples.Ram.AmortizedClear
import Examples.Ram.Arithmetic
import Examples.Ram.ArrayArguments
import Examples.Ram.ArrayCopy
import Examples.Ram.ArrayCopyFunction
import Examples.Ram.FunctionComposition
import Examples.Ram.FunctionCompositionTime
import Examples.Ram.ArraySum
import Examples.Ram.ArrayCount
import Examples.Ram.ArrayFold
import Examples.Ram.ArrayMap
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySliceProperties
import Examples.Ram.BinarySearch
import Examples.Ram.BitLength
import Examples.Ram.Composition
import Examples.Ram.ContractFill
import Examples.Ram.Factorial
import Examples.Ram.FactorialFunction
import Examples.Ram.FactorialStream
import Examples.Ram.FunctionRun
import Examples.Ram.LocalBindings
import Examples.Ram.LowerBound
import Examples.Ram.GraphDegree
import Examples.Ram.InsertionSort
import Examples.Ram.LocalCalls
import Examples.Ram.Merge
import Examples.Ram.MergeSort
import Examples.Ram.Named
import Examples.Ram.ProblemArithmetic
import Examples.Ram.Syntax
import Examples.Ram.TriangularLoop
import Examples.Ram.Verification

/-!
# Examples of verified programming and complexity proofs

These programs exercise the library's syntax, correctness and resource interfaces.
They are downstream consumers: `import Complexity` does not import this module.
The executable driver is in `Examples.Main`.
-/
