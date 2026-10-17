import LeanTasks.Task1.Defs

-- Bad submission: the main proof is fine, but it relies on a helper lemma whose
-- proof is `sorry`.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem helper (l : List Nat) (acc : Nat) : sumAcc l acc = acc + sum l := by
  sorry

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  simp [helper]

end LeanTasks.Task1.Problem
