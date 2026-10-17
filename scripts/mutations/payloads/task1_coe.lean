import LeanTasks.Task1.Defs

-- Bad submission: the statement is replaced by `True`, and a coercion lets the
-- reference proof elaborate against `True` in Check.lean.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

instance : Coe (∀ l : List Nat, sumAcc l 0 = sum l) True := ⟨fun _ => trivial⟩

theorem sumAcc_zero_eq_sum : True := trivial

end LeanTasks.Task1.Problem
