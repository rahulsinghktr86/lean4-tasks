import LeanTasks.Task3.Defs
import LeanTasks.Task3.Solution

/-!
# Task 3 — Calibration

Machine-checked evidence for the difficulty statements in `Problem.lean`.
Each `fails_to_close` line shows that an automated attempt does *not* solve
the problem; the goal is then closed with the reference solution.
-/

namespace LeanTasks.Task3.Calibration

open LeanTasks.Task3

/-- `fails_to_close t` succeeds iff the tactic `t` either fails or leaves goals
open, i.e. iff `t` does *not* prove the goal. -/
macro "fails_to_close " t:tacticSeq : tactic => `(tactic| fail_if_success (($t); done))

-- The attempts below fail on purpose; do not lint their unused simp arguments.
set_option linter.unusedSimpArgs false

-- Sanity checks for `fails_to_close` itself: it accepts a tactic that leaves the
-- goal open, and it rejects a tactic that proves the goal.
example : True := by
  fails_to_close skip
  trivial
example : True := by
  fail_if_success (fails_to_close trivial)
  trivial

/-! ## Direct automation fails on each statement -/

example (l : List Nat) : Sorted (insertionSort l) := by
  fails_to_close grind [insertionSort, insertSorted, Sorted]
  fails_to_close simp_all [insertionSort, insertSorted]
  fails_to_close (induction l <;> simp_all [insertionSort, insertSorted])
  fails_to_close (induction l <;> grind [insertionSort, insertSorted, Sorted])
  exact Solution.insertionSort_sorted l

example (l : List Nat) : (insertionSort l).Perm l := by
  fails_to_close grind [insertionSort, insertSorted]
  fails_to_close simp_all [insertionSort, insertSorted]
  fails_to_close (induction l <;> simp_all [insertionSort, insertSorted])
  fails_to_close (induction l <;> grind [insertionSort, insertSorted])
  exact Solution.insertionSort_perm l

example {l₁ l₂ : List Nat} (h₁ : Sorted l₁) (h₂ : Sorted l₂) (hp : l₁.Perm l₂) :
    l₁ = l₂ := by
  fails_to_close grind [Sorted]
  fails_to_close simp_all
  fails_to_close (induction h₁ generalizing l₂ <;> grind [Sorted])
  fails_to_close (induction l₁ generalizing l₂ <;> grind [Sorted])
  exact Solution.sorted_perm_unique h₁ h₂ hp

example {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) : insertionSort l₁ = insertionSort l₂ := by
  fails_to_close grind [insertionSort, insertSorted]
  fails_to_close simp_all [insertionSort, insertSorted]
  fails_to_close (induction hp <;> grind [insertionSort, insertSorted])
  exact Solution.insertionSort_eq_of_perm hp

/-! ## Shortcuts, disclosed so that the difficulty rating is honest -/

-- The auxiliary fact for part 1 closes with one nested automation call.
example (x : Nat) (l : List Nat) (h : Sorted l) : Sorted (insertSorted x l) := by
  induction l <;> grind [intro Sorted, cases Sorted, insertSorted]

-- Parts 1, 2 and 4 each close with a short script that nests a second induction.
example (l : List Nat) : Sorted (insertionSort l) := by
  induction l with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [insertionSort]
    generalize insertionSort xs = m at ih
    induction m <;> grind [intro Sorted, cases Sorted, insertSorted]

example (l : List Nat) : (insertionSort l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertionSort]
    refine List.Perm.trans ?_ (ih.cons x)
    clear ih
    generalize insertionSort xs = m
    induction m <;> grind [insertSorted, List.Perm.swap, List.Perm.cons, List.Perm.trans]

example {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) : insertionSort l₁ = insertionSort l₂ := by
  induction hp with
  | swap x y l =>
    simp only [insertionSort]
    generalize insertionSort l = m
    induction m <;> grind [insertSorted]
  | _ => grind [insertionSort]

-- Part 3 via core's `List.Perm.eq_of_pairwise` (allowed; see `Problem.lean`).
example {l₁ l₂ : List Nat} (h₁ : Sorted l₁) (h₂ : Sorted l₂) (hp : l₁.Perm l₂) :
    l₁ = l₂ := by
  have key : ∀ l, Sorted l → l.Pairwise (· ≤ ·) := by
    intro l h; induction h <;> grind [List.pairwise_cons, List.Pairwise.nil]
  exact hp.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm) (key _ h₁) (key _ h₂)

end LeanTasks.Task3.Calibration
