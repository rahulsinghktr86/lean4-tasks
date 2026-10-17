import LeanTasks.Task4.Defs

/-!
# Task 4 — A verified compiler: correct and injective

* **Difficulty:** medium
* **Mathlib:** not allowed (core Lean 4 only)
* **Topic:** structural induction on syntax, strengthening an induction
  hypothesis, injectivity of a compiler

1. **Correctness.** Running the compiled code of `e` on any stack `s` succeeds
   and pushes exactly the value of `e`. In particular, compiled code never
   underflows.
2. **Injectivity.** Different expressions compile to different code, so no
   information is lost in compilation.

Replace each `sorry` with a proof. Do not change the statements or `Defs.lean`.
Helper lemmas and helper definitions are allowed. Import nothing but
`LeanTasks.Task4.Defs`.

*Hints:* for part 1, a bare induction on `e` gets stuck in the binary cases,
because `compile a` is followed by more code. Find a more general statement
that the induction can carry. For part 2, a direct induction on two
expressions runs into equations between appended lists of different shapes,
so a different idea is needed.
(`Calibration.lean` checks that the obvious one-line attempts fail.)
-/

namespace LeanTasks.Task4.Problem

open LeanTasks.Task4

theorem compile_correct (env : Env) (e : Expr) (s : List Nat) :
    exec env (compile e) s = some (eval env e :: s) := by
  sorry

theorem compile_injective : Function.Injective compile := by
  sorry

end LeanTasks.Task4.Problem
