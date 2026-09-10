/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax

/-!
# An in-place splay access

The three borrowed arrays store immutable keys and mutable left/right child
indices. Zero denotes an empty subtree; nonzero indices name stable nodes.
`splay` returns the new root after an ordinary key search, including unsuccessful
searches. Its recursive calls descend by two edges and its rotations implement
zig, zig-zig and zig-zag, not the different move-to-root algorithm.

The declaration is the sole executable implementation. No mathematical tree is
passed to it, and no host tree operation replaces any of its reads or writes.
The source contracts establish valid indices and successful termination;
separate backend contracts account for finite words, storage and execution cost.
-/

namespace Complexity.Language.Examples.Splay

source_program Implementation where
  def rotateRight (left : Buffer Nat) (right : Buffer Nat) (root : Nat) : Nat := do
    let child ← left.get root
    let middle ← right.get child
    left.set root middle
    right.set child root
    return child

  def rotateLeft (left : Buffer Nat) (right : Buffer Nat) (root : Nat) : Nat := do
    let child ← right.get root
    let middle ← left.get child
    right.set root middle
    left.set child root
    return child

  def splay (keys : Buffer Nat) (left : Buffer Nat) (right : Buffer Nat)
      (root : Nat) (key : Nat) : Nat := do
    if root == 0 then
      return 0
    else
      let rootKey ← keys.get root
      if key < rootKey then
        let child ← left.get root
        if child == 0 then
          return root
        else
          let childKey ← keys.get child
          if key < childKey then
            let grandchild ← left.get child
            let newGrandchild ← splay keys left right grandchild key
            left.set child newGrandchild
            let moved ← rotateRight left right root
            let remaining ← left.get moved
            if remaining == 0 then
              return moved
            else
              let result ← rotateRight left right moved
              return result
          else
            if childKey < key then
              let grandchild ← right.get child
              let newGrandchild ← splay keys left right grandchild key
              right.set child newGrandchild
              if newGrandchild == 0 then
                let result ← rotateRight left right root
                return result
              else
                let moved ← rotateLeft left right child
                left.set root moved
                let result ← rotateRight left right root
                return result
            else
              let result ← rotateRight left right root
              return result
      else
        if rootKey < key then
          let child ← right.get root
          if child == 0 then
            return root
          else
            let childKey ← keys.get child
            if childKey < key then
              let grandchild ← right.get child
              let newGrandchild ← splay keys left right grandchild key
              right.set child newGrandchild
              let moved ← rotateLeft left right root
              let remaining ← right.get moved
              if remaining == 0 then
                return moved
              else
                let result ← rotateLeft left right moved
                return result
            else
              if key < childKey then
                let grandchild ← left.get child
                let newGrandchild ← splay keys left right grandchild key
                left.set child newGrandchild
                if newGrandchild == 0 then
                  let result ← rotateLeft left right root
                  return result
                else
                  let moved ← rotateRight left right child
                  right.set root moved
                  let result ← rotateLeft left right root
                  return result
              else
                let result ← rotateLeft left right root
                return result
        else
          return root

end Complexity.Language.Examples.Splay
