import LeanTasks.Task4.Defs

/-!
# Task 4 — Unit tests for the definitions

Imports only `Defs.lean`, so these tests run even if a proof elsewhere breaks.
All tests are kernel-checked (`decide` / `rfl`), not run in compiled code.
-/

namespace LeanTasks.Task4.Test

open LeanTasks.Task4

/-- `x = 3`, `y = 4`, every other variable is `0`. -/
def env : Env := fun v => if v = "x" then 3 else if v = "y" then 4 else 0

/-- `(x + 2) * y` -/
def sample : Expr := .mul (.add (.var "x") (.num 2)) (.var "y")

/-- `10 - x`. Detects swapped operands, since `x - 10 = 0`. -/
def sampleSub : Expr := .sub (.num 10) (.var "x")

example : eval env sample = 20 := by decide
example : eval env sampleSub = 7 := by decide
example : compile sample = [.load "x", .push 2, .add, .load "y", .mul] := by decide
example : compile sampleSub = [.push 10, .load "x", .sub] := by decide
example : exec env (compile sample) [] = some [20] := by decide
example : exec env (compile sample) [7, 8] = some [20, 7, 8] := by decide
example : exec env (compile sampleSub) [] = some [7] := by decide
-- Underflow is reported as `none`.
example : exec env [.add] [1] = none := by decide
example : exec env [.push 1, .sub] [] = none := by decide
example : exec env [.mul] [] = none := by decide
-- Distinct expressions with the same value still compile differently.
example : compile (.add (.num 1) (.num 2)) ≠ compile (.num 3) := by decide

/-! Pin every defining equation of `eval`, `compile` and `exec`. -/

section Pins
variable (ρ : Env) (n : Nat) (x : String) (a b : Expr) (p : List Instr) (u v : Nat) (s : List Nat)

example : eval ρ (.num n) = n := rfl
example : eval ρ (.var x) = ρ x := rfl
example : eval ρ (.add a b) = eval ρ a + eval ρ b := rfl
example : eval ρ (.sub a b) = eval ρ a - eval ρ b := rfl
example : eval ρ (.mul a b) = eval ρ a * eval ρ b := rfl

example : compile (.num n) = [.push n] := rfl
example : compile (.var x) = [.load x] := rfl
example : compile (.add a b) = compile a ++ compile b ++ [.add] := rfl
example : compile (.sub a b) = compile a ++ compile b ++ [.sub] := rfl
example : compile (.mul a b) = compile a ++ compile b ++ [.mul] := rfl

example : exec ρ [] s = some s := rfl
example : exec ρ (.push n :: p) s = exec ρ p (n :: s) := rfl
example : exec ρ (.load x :: p) s = exec ρ p (ρ x :: s) := rfl
-- Binary instructions: `v` is on top, and `u op v` is pushed.
example : exec ρ (.add :: p) (v :: u :: s) = exec ρ p ((u + v) :: s) := rfl
example : exec ρ (.sub :: p) (v :: u :: s) = exec ρ p ((u - v) :: s) := rfl
example : exec ρ (.mul :: p) (v :: u :: s) = exec ρ p ((u * v) :: s) := rfl
-- ... and they fail on a stack with fewer than two elements.
example : exec ρ (.add :: p) [] = none := rfl
example : exec ρ (.add :: p) [v] = none := rfl
example : exec ρ (.sub :: p) [] = none := rfl
example : exec ρ (.sub :: p) [v] = none := rfl
example : exec ρ (.mul :: p) [] = none := rfl
example : exec ρ (.mul :: p) [v] = none := rfl

end Pins

end LeanTasks.Task4.Test
