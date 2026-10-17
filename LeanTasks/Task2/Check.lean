import LeanTasks.AxiomCheck
import LeanTasks.Task2.Problem
import LeanTasks.Task2.Solution

/-!
# Task 2 — Consistency checks for the repository's own files

Part of the default build. These checks trust `Problem.lean` (they import it),
so they confirm that the task as published is consistent; they are not a
grader. Submissions are graded by `scripts/grade.sh`.
-/

namespace LeanTasks.Task2.Check

open LeanTasks.Task2

-- The problem statements are exactly the statements the reference solution proves.
example : type_of% @Problem.sumTo_eq := @Solution.sumTo_eq
example : type_of% @Problem.sumCubes_eq := @Solution.sumCubes_eq

-- The reference solution uses only the standard axioms.
#assert_standard_axioms LeanTasks.Task2.Solution.sumTo_eq
#assert_standard_axioms LeanTasks.Task2.Solution.sumCubes_eq

end LeanTasks.Task2.Check
