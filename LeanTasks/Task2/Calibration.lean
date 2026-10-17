import LeanTasks.Task2.Defs
import LeanTasks.Task2.Solution

/-!
# Task 2 — Calibration

Machine-checked evidence for the difficulty statements in `Problem.lean`.
Each `fails_to_close` line shows that an automated attempt does *not* solve
the problem; the goal is then closed with the reference solution.
-/

namespace LeanTasks.Task2.Calibration

open LeanTasks.Task2

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

/-! ## Part 1 is a warm-up -/

example (n : Nat) : sumTo n = n * (n + 1) / 2 := by fun_induction sumTo n <;> grind
example (n : Nat) : sumTo n = n * (n + 1) / 2 := by fun_induction sumTo n <;> lia
example (n : Nat) : sumTo n = n * (n + 1) / 2 := by induction n <;> grind [sumTo]

/-! ## Part 2: one-step induction plus automation fails -/

example (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  fails_to_close (induction n <;> grind [sumCubes, sumTo])
  fails_to_close (fun_induction sumCubes n <;> grind [sumTo])
  fails_to_close (fun_induction sumCubes n <;> lia)
  fails_to_close
    (induction n <;> simp_all [sumCubes, sumTo, Nat.pow_succ, Nat.mul_add, Nat.add_mul] <;> omega)
  exact Solution.sumCubes_eq n

/-! ## Shortcuts, disclosed so that the difficulty rating is honest -/

-- With the division-free Gauss identity available, `grind` does the rest.
example (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  fun_induction sumCubes n <;> grind [sumTo, Solution.two_mul_sumTo]

-- A strong induction over the three previous cases closes part 2 with `grind`
-- alone: grind's ring solver derives the Gauss identity from three consecutive
-- instances of the induction hypothesis.
example (n : Nat) : sumCubes n = sumTo n ^ 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih => rcases n with _ | _ | _ | n <;> grind [sumCubes, sumTo]

end LeanTasks.Task2.Calibration
