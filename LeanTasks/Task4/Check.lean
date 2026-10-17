import LeanTasks.AxiomCheck
import LeanTasks.Task4.Problem
import LeanTasks.Task4.Solution

/-!
# Task 4 — Consistency checks for the repository's own files

Part of the default build. These checks trust `Problem.lean` (they import it),
so they confirm that the task as published is consistent; they are not a
grader. Submissions are graded by `scripts/grade.sh`.
-/

namespace LeanTasks.Task4.Check

open LeanTasks.Task4

-- The problem statements are exactly the statements the reference solution proves.
example : type_of% @Problem.compile_correct := @Solution.compile_correct
example : type_of% @Problem.compile_injective := @Solution.compile_injective

-- The reference solution uses only the standard axioms.
#assert_standard_axioms LeanTasks.Task4.Solution.compile_correct
#assert_standard_axioms LeanTasks.Task4.Solution.compile_injective

end LeanTasks.Task4.Check
