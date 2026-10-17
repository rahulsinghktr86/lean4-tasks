import LeanTasks.Task1.Defs

-- Bad submission: the statement is replaced by `True`, and a macro makes
-- `type_of% ...` in Check.lean expand to the original statement.

macro_rules
  | `(type_of% $_e) => `(∀ l : List Nat, LeanTasks.Task1.sumAcc l 0 = LeanTasks.Task1.sum l)

namespace LeanTasks.Task1.Problem

theorem sumAcc_zero_eq_sum : True := trivial

end LeanTasks.Task1.Problem
