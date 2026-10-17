import LeanTasks.Task3.Defs

/-!
# Task 3 — Insertion sort is correct, and sorted output is unique

* **Difficulty:** easy–medium
* **Mathlib:** not allowed (core Lean 4 only; core's `List.Perm` and
  `List.Pairwise` API may be used)
* **Topic:** user-defined inductive predicates, permutations, nested induction

A sorting function is correct when its output is sorted **and** is a
permutation of its input. Neither property alone is enough: `fun _ => []` is
always sorted, and `id` is always a permutation. Prove both for
`insertionSort` (parts 1 and 2).

Then show that the specification pins down the output: two sorted lists that
are permutations of each other are equal (part 3). As a consequence,
`insertionSort` returns the same list for any reordering of its input (part 4).

Replace each `sorry` with a proof. Do not change the statements or `Defs.lean`.
Helper lemmas are allowed. Import nothing but `LeanTasks.Task3.Defs`.

Core already proves part 3 for `List.Pairwise`: `List.Perm.eq_of_pairwise`.
You may use it, after relating `Sorted` to `List.Pairwise (· ≤ ·)`, or prove
part 3 by hand. None of the four statements falls to a single `grind`,
`simp_all` or `induction … <;> grind` call; parts 1, 2 and 4 do fall to short
scripts that nest a second induction (`Calibration.lean` checks both claims).

*Hints:* parts 1 and 2 each need an auxiliary fact about `insertSorted`, proved
by its own induction. For part 1, induction on the list works if, in the step,
you also case-split on the tail and on the `if` in `insertSorted`; alternatively,
generalize over a lower bound for the head. For part 3 by hand, first show that
the head of a sorted list is `≤` every element of its tail, then compare the
heads of the two lists.
-/

namespace LeanTasks.Task3.Problem

open LeanTasks.Task3

theorem insertionSort_sorted (l : List Nat) : Sorted (insertionSort l) := by
  sorry

theorem insertionSort_perm (l : List Nat) : (insertionSort l).Perm l := by
  sorry

theorem sorted_perm_unique {l₁ l₂ : List Nat} (h₁ : Sorted l₁) (h₂ : Sorted l₂)
    (hp : l₁.Perm l₂) : l₁ = l₂ := by
  sorry

theorem insertionSort_eq_of_perm {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) :
    insertionSort l₁ = insertionSort l₂ := by
  sorry

end LeanTasks.Task3.Problem
