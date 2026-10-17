import LeanTasks.Task1.Defs
import LeanTasks.Task1.Solution

/-!
# Task 1 — Calibration

Machine-checked evidence for the difficulty statements in `Problem.lean`.
Each `fails_to_close` line shows that an obvious automated attempt does *not*
solve the problem; the goal is then closed with the reference solution.
-/

namespace LeanTasks.Task1.Calibration

open LeanTasks.Task1

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

-- A direct induction on `l` gets stuck, because the accumulator changes in the
-- recursive call.
example (l : List Nat) : sumAcc l 0 = sum l := by
  fails_to_close grind [sumAcc, sum]
  fails_to_close (induction l <;> simp_all [sumAcc, sum])
  fails_to_close (induction l <;> grind [sumAcc, sum])
  fails_to_close (fun_induction sum l <;> grind [sumAcc, sum])
  exact Solution.sumAcc_zero_eq_sum l

-- Once the statement is generalized over the accumulator, automation finishes it.
example (l : List Nat) (acc : Nat) : sumAcc l acc = acc + sum l := by
  induction l generalizing acc <;> grind [sumAcc, sum]

end LeanTasks.Task1.Calibration
