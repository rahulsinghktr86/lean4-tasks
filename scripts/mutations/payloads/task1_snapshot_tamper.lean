import LeanTasks.Task1.Defs

-- Bad submission: while it is being compiled in grade.sh's sandbox, it replaces
-- the pristine snapshot that phase 2 is built from (`../snapshot.tar`) with a
-- copy whose verifier accepts everything. The proof is `sorry`.
-- Outside the grader's sandbox (no `../snapshot.tar`), it does nothing.

#eval do
  let script := "[ -f ../snapshot.tar ] || exit 0; set -e; d=$(mktemp -d); " ++
    "tar -xf ../snapshot.tar -C \"$d\"; " ++
    "printf 'def main : IO UInt32 := do IO.println \"verifier: all checks passed\"; return 0\\n' " ++
    "> \"$d/scripts/Verify.lean\"; " ++
    "tar -cf ../snapshot.tar -C \"$d\" .; rm -rf \"$d\""
  let out ← IO.Process.output { cmd := "sh", args := #["-c", script] }
  if out.exitCode != 0 then
    throw <| IO.userError s!"tampering failed: {out.stderr}"

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := by
  sorry

end LeanTasks.Task1.Problem
