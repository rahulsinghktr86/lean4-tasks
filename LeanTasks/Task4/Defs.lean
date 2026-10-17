/-!
# Task 4 — Definitions: expressions and a stack machine

Do not modify this file. Both `Problem.lean` and `Solution.lean` import it.
-/

namespace LeanTasks.Task4

/-- Arithmetic expressions over natural numbers with named variables.
`sub` is truncated subtraction, so the order of operands matters. -/
inductive Expr where
  | num : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Variable environment. -/
abbrev Env := String → Nat

/-- Denotational semantics. -/
def eval (env : Env) : Expr → Nat
  | .num n => n
  | .var x => env x
  | .add a b => eval env a + eval env b
  | .sub a b => eval env a - eval env b
  | .mul a b => eval env a * eval env b

/-- Instructions of a simple stack machine. -/
inductive Instr where
  | push : Nat → Instr
  | load : String → Instr
  | add : Instr
  | sub : Instr
  | mul : Instr
  deriving Repr, DecidableEq

/-- Run a program on a stack (head = top). A binary instruction pops `b` (top)
and then `a`, and pushes `a op b`. Returns `none` on stack underflow. -/
def exec (env : Env) : List Instr → List Nat → Option (List Nat)
  | [], s => some s
  | .push n :: p, s => exec env p (n :: s)
  | .load x :: p, s => exec env p (env x :: s)
  | .add :: p, b :: a :: s => exec env p ((a + b) :: s)
  | .sub :: p, b :: a :: s => exec env p ((a - b) :: s)
  | .mul :: p, b :: a :: s => exec env p ((a * b) :: s)
  | .add :: _, _ => none
  | .sub :: _, _ => none
  | .mul :: _, _ => none

/-- Compile an expression to postfix stack code. -/
def compile : Expr → List Instr
  | .num n => [.push n]
  | .var x => [.load x]
  | .add a b => compile a ++ compile b ++ [.add]
  | .sub a b => compile a ++ compile b ++ [.sub]
  | .mul a b => compile a ++ compile b ++ [.mul]

end LeanTasks.Task4
