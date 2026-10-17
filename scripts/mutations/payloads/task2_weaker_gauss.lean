import LeanTasks.Task2.Defs

-- Bad submission: part 1 proves a weaker statement (an inequality).

namespace LeanTasks.Task2.Problem

open LeanTasks.Task2

theorem sumTo_eq (n : Nat) : sumTo n ≤ n * (n + 1) := by
  induction n <;> grind [sumTo]

theorem sumCubes_eq (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih => rcases n with _ | _ | _ | n <;> grind [sumCubes, sumTo]

end LeanTasks.Task2.Problem
