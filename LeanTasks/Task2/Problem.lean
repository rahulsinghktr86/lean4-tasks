import LeanTasks.Task2.Defs

/-!
# Task 2 — Gauss's formula and Nicomachus's theorem

* **Difficulty:** easy
* **Mathlib:** not allowed (core Lean 4 only: no `ring`, `linarith`, `nlinarith`;
  core's `omega`, `simp`, `grind` and `lia` are allowed)
* **Topic:** induction, finding an auxiliary identity, nonlinear `Nat` arithmetic

Prove two classical closed forms:

1. **Gauss:** `0 + 1 + ⋯ + n = n * (n + 1) / 2`, with truncated `Nat` division.
2. **Nicomachus:** `0³ + 1³ + ⋯ + n³ = (0 + 1 + ⋯ + n)²`.

Replace each `sorry` with a proof. Do not change the statements or `Defs.lean`.
Helper lemmas are allowed. Import nothing but `LeanTasks.Task2.Defs`.

Part 1 is a warm-up: after `fun_induction sumTo n`, plain `grind` or `lia`
closes it (after `induction n`, use `grind [sumTo]`). For part 2, a one-step
induction (`induction n` or `fun_induction sumCubes n`) followed by `grind`,
`lia` or `simp` + `omega` fails: the inductive step needs a fact about
`sumTo n` that the induction hypothesis does not provide.
(`Calibration.lean` checks these claims.)

*Hints:* look for a version of Gauss's formula that has no division in it.
If you do the arithmetic by hand, `omega` treats a product of two variables
as an opaque atom, so distribute products first (`Nat.mul_add`, `Nat.add_mul`).
-/

namespace LeanTasks.Task2.Problem

open LeanTasks.Task2

theorem sumTo_eq (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  sorry

theorem sumCubes_eq (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  sorry

end LeanTasks.Task2.Problem
