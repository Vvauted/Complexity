/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.List.Nat.InsertIdx
import Init.Data.List.Nat.TakeDrop

/-!
# List contents of an in-place right shift

The cursor separates the unchanged prefix from the suffix already shifted
one position to the right. This is a logical view using standard list
operations, not a second executable insertion algorithm.
-/

namespace List.Insertion

/-- The extra allocated word is initially arbitrary. Moving the cursor left
duplicates the preceding element into the cursor's current position. -/
def contents (xs : List α) (spare : α) (cursor : Nat) : List α :=
  (xs ++ [spare]).take (cursor + 1) ++ xs.drop cursor

theorem contents_length (xs : List α) (spare : α) {cursor : Nat}
    (hc : cursor ≤ xs.length) :
    (contents xs spare cursor).length = xs.length + 1 := by
  simp only [contents, List.length_append, List.length_take, List.length_drop,
    List.length_cons, List.length_nil]
  omega

theorem contents_initial (xs : List α) (spare : α) :
    contents xs spare xs.length = xs ++ [spare] := by
  simp only [contents, List.take_length_add_append, List.take_succ_cons,
    List.take_zero, List.drop_length, List.append_nil]

/-- The next word read by the right-shift loop still has its original value. -/
theorem contents_getElem_pred (xs : List α) (spare : α) {cursor : Nat}
    (hpos : 0 < cursor) (hc : cursor ≤ xs.length) :
    (contents xs spare cursor)[cursor - 1]'(by
      rw [contents_length xs spare hc]
      omega) = xs[cursor - 1]'(by omega) := by
  have htake : ((xs ++ [spare]).take (cursor + 1)).length = cursor + 1 := by
    apply List.length_take_of_le
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hpre : cursor - 1 < ((xs ++ [spare]).take (cursor + 1)).length := by
    rw [htake]
    omega
  unfold contents
  rw [List.getElem_append_left hpre, List.getElem_take,
    List.getElem_append_left (by omega : cursor - 1 < xs.length)]

/-- Filling the cursor's position gives the usual prefix/insertion/suffix
decomposition, including insertion at the original length. -/
theorem contents_set (xs : List α) (spare key : α) {cursor : Nat}
    (hc : cursor ≤ xs.length) :
    (contents xs spare cursor).set cursor key =
      xs.take cursor ++ key :: xs.drop cursor := by
  have htake : ((xs ++ [spare]).take (cursor + 1)).length = cursor + 1 := by
    apply List.length_take_of_le
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hbound : cursor < (contents xs spare cursor).length := by
    rw [contents_length xs spare hc]
    omega
  rw [List.set_eq_take_append_cons_drop, if_pos hbound]
  unfold contents
  rw [List.take_append_of_le_length (by omega :
      cursor ≤ ((xs ++ [spare]).take (cursor + 1)).length),
    List.take_take, Nat.min_eq_left (by omega : cursor ≤ cursor + 1),
    List.take_append_of_le_length hc, List.drop_left' htake]

theorem contents_shift (xs : List α) (spare : α) {cursor : Nat}
    (hpos : 0 < cursor) (hc : cursor ≤ xs.length) :
    (contents xs spare cursor).set cursor (xs[cursor - 1]'(by omega)) =
      contents xs spare (cursor - 1) := by
  rw [contents_set xs spare _ hc]
  have hpred : cursor - 1 < xs.length := by omega
  have hstep : cursor - 1 + 1 = cursor := by omega
  unfold contents
  rw [hstep, List.take_append_of_le_length hc,
    List.drop_eq_getElem_cons hpred, hstep]

theorem insertIdx_eq_take_cons_drop (xs : List α) (key : α) {p : Nat}
    (hp : p ≤ xs.length) :
    xs.insertIdx p key = xs.take p ++ key :: xs.drop p := by
  induction p generalizing xs with
  | zero => simp
  | succ p ih =>
      cases xs with
      | nil => simp at hp
      | cons x xs =>
          have hp' : p ≤ xs.length := Nat.le_of_succ_le_succ hp
          simpa only [List.insertIdx_succ_cons, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append] using
            congrArg (List.cons x) (ih xs hp')

theorem contents_set_eq_insertIdx (xs : List α) (spare key : α) {p : Nat}
    (hp : p ≤ xs.length) :
    (contents xs spare p).set p key = xs.insertIdx p key := by
  rw [contents_set xs spare key hp, insertIdx_eq_take_cons_drop xs key hp]

end List.Insertion
