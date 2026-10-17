/-!
# Task 3 — Definitions: insertion sort

Do not modify this file. Both `Problem.lean` and `Solution.lean` import it.
-/

namespace LeanTasks.Task3

/-- Insert `x` into a list, before the first element that is `≥ x`. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Insertion sort. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (insertionSort xs)

/-- A list is sorted (non-decreasing) when each adjacent pair is in order. -/
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons (x y : Nat) (rest : List Nat) : x ≤ y → Sorted (y :: rest) → Sorted (x :: y :: rest)

end LeanTasks.Task3
