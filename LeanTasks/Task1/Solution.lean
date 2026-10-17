import LeanTasks.Task1.Defs

/-!
# Task 1 — Reference solution
-/

namespace LeanTasks.Task1.Solution

open LeanTasks.Task1

/-- Generalized invariant: the accumulator is simply added to the remaining sum. -/
theorem sumAcc_eq (l : List Nat) (acc : Nat) : sumAcc l acc = acc + sum l := by
  induction l generalizing acc with
  | nil => simp [sumAcc, sum]
  | cons x xs ih =>
    simp only [sumAcc, sum, ih]
    omega

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  simp [sumAcc_eq]

end LeanTasks.Task1.Solution
