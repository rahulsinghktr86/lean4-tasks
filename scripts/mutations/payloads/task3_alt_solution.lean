import LeanTasks.Task3.Defs

-- Good submission: a different solution; part 3 uses core's
-- `List.Perm.eq_of_pairwise` (allowed by the task).

namespace LeanTasks.Task3.Problem

open LeanTasks.Task3

theorem insertSorted_sorted (x : Nat) (l : List Nat) (h : Sorted l) :
    Sorted (insertSorted x l) := by
  induction l <;> grind [intro Sorted, cases Sorted, insertSorted]

theorem insertSorted_perm (x : Nat) (l : List Nat) : (insertSorted x l).Perm (x :: l) := by
  induction l with
  | nil => exact .refl _
  | cons y ys ih =>
    unfold insertSorted
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap x y ys)

theorem insertionSort_sorted (l : List Nat) : Sorted (insertionSort l) := by
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact insertSorted_sorted x _ ih

theorem insertionSort_perm (l : List Nat) : (insertionSort l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insertSorted_perm x _).trans (ih.cons x)

theorem sorted_pairwise (l : List Nat) (h : Sorted l) : l.Pairwise (· ≤ ·) := by
  induction h <;> grind [List.pairwise_cons, List.Pairwise.nil]

theorem sorted_perm_unique {l₁ l₂ : List Nat} (h₁ : Sorted l₁) (h₂ : Sorted l₂)
    (hp : l₁.Perm l₂) : l₁ = l₂ :=
  hp.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm) (sorted_pairwise _ h₁) (sorted_pairwise _ h₂)

theorem insertionSort_eq_of_perm {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) :
    insertionSort l₁ = insertionSort l₂ :=
  sorted_perm_unique (insertionSort_sorted l₁) (insertionSort_sorted l₂)
    (((insertionSort_perm l₁).trans hp).trans (insertionSort_perm l₂).symm)

end LeanTasks.Task3.Problem
