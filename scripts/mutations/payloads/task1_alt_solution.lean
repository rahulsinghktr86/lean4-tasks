import LeanTasks.Task1.Defs

-- Good submission: a correct proof that differs from the reference solution.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  suffices h : ∀ acc, sumAcc l acc = acc + sum l by simpa using h 0
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; simp only [sumAcc, sum, ih]; omega

end LeanTasks.Task1.Problem
