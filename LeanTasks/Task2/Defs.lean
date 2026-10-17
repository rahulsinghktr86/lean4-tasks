/-!
# Task 2 — Definitions: sums of naturals and of cubes

Do not modify this file. Both `Problem.lean` and `Solution.lean` import it.
-/

namespace LeanTasks.Task2

/-- `sumTo n = 0 + 1 + ⋯ + n`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- `sumCubes n = 0³ + 1³ + ⋯ + n³`. -/
def sumCubes : Nat → Nat
  | 0 => 0
  | n + 1 => sumCubes n + (n + 1) ^ 3

end LeanTasks.Task2
