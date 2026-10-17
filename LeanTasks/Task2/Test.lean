import LeanTasks.Task2.Defs

/-!
# Task 2 — Unit tests for the definitions

Imports only `Defs.lean`, so these tests run even if a proof elsewhere breaks.
All tests are kernel-checked (`decide` / `rfl`), not run in compiled code.
-/

namespace LeanTasks.Task2.Test

open LeanTasks.Task2

example : sumTo 0 = 0 := by decide
example : sumTo 4 = 10 := by decide
example : sumTo 100 = 5050 := by decide
example : sumCubes 0 = 0 := by decide
example : sumCubes 4 = 100 := by decide   -- 1 + 8 + 27 + 64
example : sumCubes 10 = 3025 := by decide
-- Both closed forms hold on an initial segment.
example : (List.range 30).all (fun n => sumTo n == n * (n + 1) / 2) = true := by decide
example : (List.range 30).all (fun n => sumCubes n == sumTo n ^ 2) = true := by decide

-- Pin every defining equation, so `Defs.lean` cannot be swapped for a closed form
-- (which would make both theorems provable by `rfl`).
example : sumTo 0 = 0 := rfl
example (n : Nat) : sumTo (n + 1) = sumTo n + (n + 1) := rfl
example : sumCubes 0 = 0 := rfl
example (n : Nat) : sumCubes (n + 1) = sumCubes n + (n + 1) ^ 3 := rfl

end LeanTasks.Task2.Test
