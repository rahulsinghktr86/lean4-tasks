import LeanTasks.Task2.Defs

-- Good submission: the automation shortcuts disclosed in Calibration.lean.

namespace LeanTasks.Task2.Problem

open LeanTasks.Task2

theorem sumTo_eq (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  fun_induction sumTo n <;> grind

theorem sumCubes_eq (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih => rcases n with _ | _ | _ | n <;> grind [sumCubes, sumTo]

end LeanTasks.Task2.Problem
