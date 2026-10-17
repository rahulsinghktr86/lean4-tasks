import LeanTasks.Task1.Defs

/-!
# Task 1 — Tail-recursive sum is correct

* **Difficulty:** easy
* **Mathlib:** not allowed (core Lean 4 only)
* **Topic:** induction, generalizing an accumulator

`sumAcc` is the tail-recursive version of `sum`. Prove that running it from an
accumulator of `0` gives the same result as the structural `sum`.

Replace the `sorry` with a proof. Do not change the statement or `Defs.lean`.
Helper lemmas are allowed. Import nothing but `LeanTasks.Task1.Defs`.

*Hint:* a direct induction on `l` gets stuck, because the accumulator changes in
the recursive call. Prove a more general statement about an arbitrary `acc` first.
(`Calibration.lean` checks that the obvious one-line attempts fail.)
-/

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  sorry

end LeanTasks.Task1.Problem
