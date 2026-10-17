import Lean
import LeanTasks.Task1.Defs

/-!
Mutation payload, not part of the build: a cheating "solution" to Task 1.
It adds a proof of `False` while kernel type checking is switched off, then uses
it. The in-Lean axiom audit cannot see this (no axioms are involved), so
`scripts/mutations/task1.sh` checks that the grader rejects it.
-/

open Lean in
set_option debug.skipKernelTC true in
run_cmd Elab.Command.liftCoreM do
  addDecl <| .thmDecl
    { name := `LeanTasks.Task1.bogus, levelParams := [],
      type := mkConst ``False, value := mkConst ``True.intro }

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l :=
  LeanTasks.Task1.bogus.elim

end LeanTasks.Task1.Problem
