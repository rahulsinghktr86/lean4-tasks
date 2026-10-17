import LeanTasks.AxiomCheck
import LeanTasks.Task3.Problem
import LeanTasks.Task3.Solution

/-!
# Task 3 — Consistency checks for the repository's own files

Part of the default build. These checks trust `Problem.lean` (they import it),
so they confirm that the task as published is consistent; they are not a
grader. Submissions are graded by `scripts/grade.sh`.
-/

namespace LeanTasks.Task3.Check

open LeanTasks.Task3

-- The problem statements are exactly the statements the reference solution proves.
example : type_of% @Problem.insertionSort_sorted := @Solution.insertionSort_sorted
example : type_of% @Problem.insertionSort_perm := @Solution.insertionSort_perm
example : type_of% @Problem.sorted_perm_unique := @Solution.sorted_perm_unique
example : type_of% @Problem.insertionSort_eq_of_perm := @Solution.insertionSort_eq_of_perm

-- The reference solution uses only the standard axioms.
#assert_standard_axioms LeanTasks.Task3.Solution.insertionSort_sorted
#assert_standard_axioms LeanTasks.Task3.Solution.insertionSort_perm
#assert_standard_axioms LeanTasks.Task3.Solution.sorted_perm_unique
#assert_standard_axioms LeanTasks.Task3.Solution.insertionSort_eq_of_perm

end LeanTasks.Task3.Check
