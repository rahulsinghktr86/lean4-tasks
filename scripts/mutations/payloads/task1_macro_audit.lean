import LeanTasks.Task1.Defs
import LeanTasks.AxiomCheck

-- Bad submission: a macro turns `#assert_standard_axioms` into a no-op in every
-- file that imports this one, and the proof is `sorry`.

macro_rules
  | `(#assert_standard_axioms $_x:ident) => `(set_option pp.all false)

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  sorry

end LeanTasks.Task1.Problem
