import LeanTasks.Task4.Defs

-- Good submission: a different proof of correctness, via a lemma about running
-- an appended program, and a decompiler-based proof of injectivity.

namespace LeanTasks.Task4.Problem

open LeanTasks.Task4

theorem exec_append (env : Env) (p q : List Instr) (s : List Nat) :
    exec env (p ++ q) s = (exec env p s).bind (exec env q) := by
  fun_induction exec env p s <;> simp_all [exec]

theorem compile_correct (env : Env) (e : Expr) (s : List Nat) :
    exec env (compile e) s = some (eval env e :: s) := by
  induction e generalizing s <;> simp_all [compile, exec, eval, exec_append]

def dec : List Instr → List Expr → Option (List Expr)
  | [], st => some st
  | .push n :: p, st => dec p (.num n :: st)
  | .load x :: p, st => dec p (.var x :: st)
  | .add :: p, b :: a :: st => dec p (.add a b :: st)
  | .sub :: p, b :: a :: st => dec p (.sub a b :: st)
  | .mul :: p, b :: a :: st => dec p (.mul a b :: st)
  | _ :: _, _ => none

theorem dec_compile (e : Expr) (p : List Instr) (st : List Expr) :
    dec (compile e ++ p) st = dec p (e :: st) := by
  induction e generalizing p st <;> simp_all [compile, dec]

theorem compile_injective : Function.Injective compile := by
  intro a b h
  have ha := dec_compile a [] []
  have hb := dec_compile b [] []
  simp only [List.append_nil] at ha hb
  rw [h, hb] at ha
  simpa [dec] using ha.symm

end LeanTasks.Task4.Problem
