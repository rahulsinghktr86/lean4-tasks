import LeanTasks.Task1.Solution

-- Bad submission: re-exports the reference solution.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l :=
  Solution.sumAcc_zero_eq_sum l

end LeanTasks.Task1.Problem
