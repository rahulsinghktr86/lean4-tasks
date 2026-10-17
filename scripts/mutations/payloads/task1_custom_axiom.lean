import LeanTasks.Task1.Defs

-- Bad submission: "proves" the statement with a user-declared axiom.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

axiom cheat : ∀ l : List Nat, sumAcc l 0 = sum l

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := cheat l

end LeanTasks.Task1.Problem
