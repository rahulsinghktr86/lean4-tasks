import LeanTasks.Task3.Defs

/-!
# Task 3 — Reference solution
-/

namespace LeanTasks.Task3.Solution

open LeanTasks.Task3

/-! ### Sortedness -/

/-- If `y ≤ x` and `y` is at most the head of a sorted list `l`, then
`y` can be put in front of `insertSorted x l`. -/
theorem sorted_cons_insertSorted {x y : Nat} {l : List Nat}
    (hyx : y ≤ x) (h : Sorted (y :: l)) : Sorted (y :: insertSorted x l) := by
  induction l generalizing y with
  | nil => exact Sorted.cons y x [] hyx (Sorted.single x)
  | cons z rest ih =>
    cases h with
    | cons _ _ _ hyz hz =>
      unfold insertSorted
      split
      · -- `x ≤ z`: the result is `y :: x :: z :: rest`
        exact Sorted.cons y x _ hyx (Sorted.cons x z rest ‹x ≤ z› hz)
      · -- `z < x`: the result is `y :: z :: insertSorted x rest`
        exact Sorted.cons y z _ hyz (ih (by omega) hz)

theorem insertSorted_sorted (x : Nat) {l : List Nat} (h : Sorted l) :
    Sorted (insertSorted x l) := by
  cases l with
  | nil => exact Sorted.single x
  | cons y ys =>
    unfold insertSorted
    split
    · exact Sorted.cons x y ys ‹x ≤ y› h
    · exact sorted_cons_insertSorted (by omega) h

theorem insertionSort_sorted (l : List Nat) : Sorted (insertionSort l) := by
  induction l with
  | nil => exact Sorted.nil
  | cons x xs ih => exact insertSorted_sorted x ih

/-! ### Permutation -/

theorem insertSorted_perm (x : Nat) (l : List Nat) : (insertSorted x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold insertSorted
    split
    · exact List.Perm.refl _
    · -- y :: insertSorted x ys ~ y :: x :: ys ~ x :: y :: ys
      exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem insertionSort_perm (l : List Nat) : (insertionSort l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (insertSorted_perm x _).trans (ih.cons x)

/-! ### Uniqueness of sorted permutations -/

theorem sorted_tail {x : Nat} {l : List Nat} (h : Sorted (x :: l)) : Sorted l := by
  cases h with
  | single => exact Sorted.nil
  | cons _ _ _ _ h' => exact h'

/-- The head of a sorted list is a lower bound for every element of its tail. -/
theorem sorted_head_le {x : Nat} {l : List Nat} (h : Sorted (x :: l)) : ∀ z ∈ l, x ≤ z := by
  induction l generalizing x with
  | nil => simp
  | cons y ys ih =>
    cases h with
    | cons _ _ _ hxy hy =>
      intro z hz
      cases hz with
      | head => exact hxy
      | tail _ hz => exact Nat.le_trans hxy (ih hy z hz)

/-- If `a :: as` and `b :: bs` are sorted permutations of each other, then `a ≤ b`:
`b` occurs somewhere in `a :: as`, and `a` is below everything there. -/
theorem head_le_head {a b : Nat} {as bs : List Nat} (h₁ : Sorted (a :: as))
    (hp : (a :: as).Perm (b :: bs)) : a ≤ b := by
  have hb : b ∈ a :: as := hp.symm.subset (List.mem_cons_self ..)
  cases hb with
  | head => exact Nat.le_refl a
  | tail _ hb => exact sorted_head_le h₁ b hb

theorem sorted_perm_unique {l₁ l₂ : List Nat} (h₁ : Sorted l₁) (h₂ : Sorted l₂)
    (hp : l₁.Perm l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact (List.perm_nil.mp hp.symm).symm
  | cons a as ih =>
    cases l₂ with
    | nil => exact absurd hp.length_eq (by simp)
    | cons b bs =>
      have hab : a = b := Nat.le_antisymm (head_le_head h₁ hp) (head_le_head h₂ hp.symm)
      subst hab
      rw [ih (sorted_tail h₁) (sorted_tail h₂) ((List.perm_cons a).mp hp)]

theorem insertionSort_eq_of_perm {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) :
    insertionSort l₁ = insertionSort l₂ :=
  sorted_perm_unique (insertionSort_sorted l₁) (insertionSort_sorted l₂)
    (((insertionSort_perm l₁).trans hp).trans (insertionSort_perm l₂).symm)

end LeanTasks.Task3.Solution
