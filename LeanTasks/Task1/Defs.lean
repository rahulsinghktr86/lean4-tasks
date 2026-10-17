/-!
# Task 1 — Definitions: accumulator-based list sum

Do not modify this file. Both `Problem.lean` and `Solution.lean` import it.
-/

namespace LeanTasks.Task1

/-- Structural (non-tail-recursive) sum of a list of naturals. -/
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

/-- Tail-recursive sum that threads an accumulator. -/
def sumAcc : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => sumAcc xs (acc + x)

end LeanTasks.Task1
