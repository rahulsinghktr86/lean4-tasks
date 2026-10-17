import LeanTasks.AxiomCheck
import LeanTasks.Task1.Problem
import LeanTasks.Task1.Solution

/-!
# Task 1 — Consistency checks for the repository's own files

Part of the default build. These checks trust `Problem.lean` (they import it),
so they confirm that the task as published is consistent; they are not a
grader. Submissions are graded by `scripts/grade.sh`.
-/

namespace LeanTasks.Task1.Check

open LeanTasks.Task1

-- The problem statement is exactly the statement the reference solution proves.
example : type_of% @Problem.sumAcc_zero_eq_sum := @Solution.sumAcc_zero_eq_sum

-- The reference solution uses only the standard axioms.
#assert_standard_axioms LeanTasks.Task1.Solution.sumAcc_zero_eq_sum

end LeanTasks.Task1.Check
