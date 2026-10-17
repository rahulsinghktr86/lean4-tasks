import LeanTasks.Task4.Defs
import LeanTasks.Task4.Solution

/-!
# Task 4 — Calibration

Machine-checked evidence for the difficulty statements in `Problem.lean`.
Each `fails_to_close` line shows that an automated attempt does *not* solve
the problem; the goal is then closed with the reference solution.
-/

namespace LeanTasks.Task4.Calibration

open LeanTasks.Task4

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

/-! ## Part 1 -/

-- A bare induction on `e` gets stuck in the binary cases.
example (env : Env) (e : Expr) (s : List Nat) :
    exec env (compile e) s = some (eval env e :: s) := by
  fails_to_close (induction e generalizing s <;> simp_all [compile, exec, eval])
  fails_to_close (induction e generalizing s <;> grind [compile, exec, eval])
  exact Solution.compile_correct env e s

-- Once the right generalization is stated, one line proves it; this is why the
-- hint does not spell the generalization out.
example (env : Env) (e : Expr) (p : List Instr) (s : List Nat) :
    exec env (compile e ++ p) s = exec env p (eval env e :: s) := by
  induction e generalizing p s <;> simp_all [compile, exec, eval]

/-! ## Part 2 -/

-- A direct induction on the two expressions does not go through.
example : Function.Injective compile := by
  fails_to_close
    (intro a b h; induction a generalizing b <;> cases b <;> simp_all [compile])
  fails_to_close
    (intro a b h; induction a generalizing b <;> cases b <;> grind [compile])
  exact Solution.compile_injective

end LeanTasks.Task4.Calibration
