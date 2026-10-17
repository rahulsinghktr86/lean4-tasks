import LeanTasks.Task4.Defs

/-!
# Task 4 — Reference solution
-/

namespace LeanTasks.Task4.Solution

open LeanTasks.Task4

/-! ### Part 1: correctness -/

/-- Generalized correctness: compiled code followed by any continuation `p`
behaves like pushing the value and then running `p`. -/
theorem exec_compile_append (env : Env) (e : Expr) (p : List Instr) (s : List Nat) :
    exec env (compile e ++ p) s = exec env p (eval env e :: s) := by
  induction e generalizing p s with
  | num n => simp [compile, exec, eval]
  | var x => simp [compile, exec, eval]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
    rw [iha, ihb]
    simp [exec, eval]

theorem compile_correct (env : Env) (e : Expr) (s : List Nat) :
    exec env (compile e) s = some (eval env e :: s) := by
  have h := exec_compile_append env e [] s
  rw [List.append_nil] at h
  rw [h, exec]

/-! ### Part 2: injectivity, via a decompiler that is a left inverse of `compile` -/

/-- Decompiler: replays the code like `exec`, but on a stack of expressions. -/
def decode : List Instr → List Expr → Option (List Expr)
  | [], st => some st
  | .push n :: p, st => decode p (.num n :: st)
  | .load x :: p, st => decode p (.var x :: st)
  | .add :: p, b :: a :: st => decode p (.add a b :: st)
  | .sub :: p, b :: a :: st => decode p (.sub a b :: st)
  | .mul :: p, b :: a :: st => decode p (.mul a b :: st)
  | .add :: _, _ => none
  | .sub :: _, _ => none
  | .mul :: _, _ => none

theorem decode_compile_append (e : Expr) (p : List Instr) (st : List Expr) :
    decode (compile e ++ p) st = decode p (e :: st) := by
  induction e generalizing p st with
  | num n => simp [compile, decode]
  | var x => simp [compile, decode]
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
    simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
    rw [iha, ihb]
    simp [decode]

theorem decode_compile (e : Expr) : decode (compile e) [] = some [e] := by
  have h := decode_compile_append e [] []
  rw [List.append_nil] at h
  rw [h, decode]

theorem compile_injective : Function.Injective compile := by
  intro e₁ e₂ h
  have h₁ := decode_compile e₁
  -- Rewriting with `h` turns `decode (compile e₁) []` into `some [e₂]`.
  rw [h, decode_compile] at h₁
  simpa using h₁.symm

end LeanTasks.Task4.Solution
