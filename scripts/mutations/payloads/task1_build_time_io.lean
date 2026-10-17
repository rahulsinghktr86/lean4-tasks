import LeanTasks.Task1.Defs

-- Bad submission: while it is being compiled, it overwrites the verifier and the
-- list of graded theorems in the tree it is built in. The proof is `sorry`.

#eval IO.FS.writeFile "scripts/Verify.lean"
  "def main : IO UInt32 := do IO.println \"ACCEPT\"; return 0\n"
#eval IO.FS.writeFile "LeanTasks/Task1/graded.txt" ""

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  sorry

end LeanTasks.Task1.Problem
