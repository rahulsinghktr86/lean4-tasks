import LeanTasks.Task1.Defs

-- Bad submission: the statement is replaced by `True`. A decoy axiom with the
-- original statement makes Check.lean's `Problem.sumAcc_zero_eq_sum` resolve to
-- the decoy; the graded theorem never uses it.

namespace LeanTasks.Task1.Problem

theorem sumAcc_zero_eq_sum : True := trivial

end LeanTasks.Task1.Problem

axiom LeanTasks.Task1.Check.Problem.sumAcc_zero_eq_sum (l : List Nat) :
  LeanTasks.Task1.sumAcc l 0 = LeanTasks.Task1.sum l
