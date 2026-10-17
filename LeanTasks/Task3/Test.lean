import LeanTasks.Task3.Defs

/-!
# Task 3 — Unit tests for the definitions

Imports only `Defs.lean`, so these tests run even if a proof elsewhere breaks.
All tests are kernel-checked (`decide` / `rfl` / explicit proofs), not run in
compiled code.
-/

namespace LeanTasks.Task3.Test

open LeanTasks.Task3

example : insertSorted 3 [1, 2, 4, 5] = [1, 2, 3, 4, 5] := by decide
example : insertSorted 0 [1, 2] = [0, 1, 2] := by decide
example : insertSorted 9 [1, 2] = [1, 2, 9] := by decide
example : insertSorted 2 [2, 2] = [2, 2, 2] := by decide
example : insertionSort [] = [] := by decide
example : insertionSort [5, 2, 4, 2, 1, 3] = [1, 2, 2, 3, 4, 5] := by decide
example : insertionSort [3, 2, 1, 0] = [0, 1, 2, 3] := by decide

-- `Sorted` is the specification, so test it in both directions: it must not be vacuous.
example : Sorted [] := .nil
example : Sorted [7] := .single 7
example : Sorted [1, 2, 2, 3] :=
  .cons 1 2 _ (by decide) (.cons 2 2 _ (by decide) (.cons 2 3 _ (by decide) (.single 3)))
example : ¬ Sorted [2, 1] := by
  intro h; cases h; omega
example : ¬ Sorted [1, 3, 2] := by
  intro h; cases h with | cons _ _ _ _ h => cases h; omega

-- Pin every defining equation.
example (x : Nat) : insertSorted x [] = [x] := rfl
example (x y : Nat) (ys : List Nat) :
    insertSorted x (y :: ys) = if x ≤ y then x :: y :: ys else y :: insertSorted x ys := rfl
example : insertionSort [] = [] := rfl
example (x : Nat) (xs : List Nat) :
    insertionSort (x :: xs) = insertSorted x (insertionSort xs) := rfl

end LeanTasks.Task3.Test
