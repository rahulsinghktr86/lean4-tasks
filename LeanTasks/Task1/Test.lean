import LeanTasks.Task1.Defs

/-!
# Task 1 — Unit tests for the definitions

Imports only `Defs.lean`, so these tests run even if a proof elsewhere breaks.
All tests are kernel-checked (`decide` / `rfl`), not run in compiled code.
-/

namespace LeanTasks.Task1.Test

open LeanTasks.Task1

example : sum [] = 0 := by decide
example : sum [1, 2, 3, 4] = 10 := by decide
example : sumAcc [1, 2, 3, 4] 0 = 10 := by decide
example : sumAcc [1, 2, 3] 100 = 106 := by decide

-- Pin every defining equation, so `Defs.lean` cannot be swapped for a closed form.
example : sum [] = 0 := rfl
example (x : Nat) (xs : List Nat) : sum (x :: xs) = x + sum xs := rfl
example (acc : Nat) : sumAcc [] acc = acc := rfl
example (x : Nat) (xs : List Nat) (acc : Nat) : sumAcc (x :: xs) acc = sumAcc xs (acc + x) := rfl

end LeanTasks.Task1.Test
