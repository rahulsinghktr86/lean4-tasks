import LeanTasks.Task2.Defs

/-!
# Task 2 — Reference solution

Done by hand, without `grind`/`lia`, to show the arithmetic explicitly.
-/

namespace LeanTasks.Task2.Solution

open LeanTasks.Task2

/-- Division-free form of Gauss's formula. -/
theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- 2 * (sumTo n + (n + 1)) = n * (n + 1) + 2 * (n + 1); factor out `n + 1`.
    -- The final `rw` closes `(n + 1) * (n + 2) = (n + 1) * (n + 1 + 1)` by `rfl`.
    rw [sumTo, Nat.mul_add, ih, Nat.mul_comm n (n + 1), Nat.mul_comm 2 (n + 1), ← Nat.mul_add]

theorem sumTo_eq (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  rw [← two_mul_sumTo n, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

/-- `(a + b)² = a² + 2ab + b²` (core Lean has no `ring`). -/
theorem add_sq (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  rw [Nat.pow_two (a + b), Nat.pow_two a, Nat.pow_two b, Nat.add_mul, Nat.mul_add, Nat.mul_add,
    Nat.mul_comm b a, Nat.mul_assoc 2 a b]
  omega

/-- The key step: `(n + 1)³ = 2 · sumTo n · (n + 1) + (n + 1)²`. -/
theorem succ_cube (n : Nat) : (n + 1) ^ 3 = 2 * sumTo n * (n + 1) + (n + 1) ^ 2 :=
  calc (n + 1) ^ 3
      = (n + 1) * (n + 1) * (n + 1) := by rw [Nat.pow_succ, Nat.pow_two]
    _ = (n * (n + 1) + (n + 1)) * (n + 1) := by rw [Nat.add_one_mul n (n + 1)]
    _ = n * (n + 1) * (n + 1) + (n + 1) * (n + 1) := Nat.add_mul ..
    _ = 2 * sumTo n * (n + 1) + (n + 1) ^ 2 := by rw [two_mul_sumTo, Nat.pow_two]

theorem sumCubes_eq (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumCubes, sumTo, ih, add_sq, succ_cube]
    omega

end LeanTasks.Task2.Solution
