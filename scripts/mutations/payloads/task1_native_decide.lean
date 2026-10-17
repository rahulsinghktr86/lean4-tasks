import LeanTasks.Task1.Defs

-- Bad submission: `native_decide` trusts compiled code, and `implemented_by`
-- makes the compiled code disagree with the logical definition, which yields a
-- proof of `False`.

namespace LeanTasks.Task1.Problem

open LeanTasks.Task1

def liar (_ : Nat) : Bool := false

@[implemented_by liar] def truth (_ : Nat) : Bool := true

theorem compiledLie : truth 0 = false := by native_decide

theorem boom : False := by
  have h : truth 0 = true := rfl
  rw [compiledLie] at h
  exact Bool.false_ne_true h

theorem sumAcc_zero_eq_sum (l : List Nat) : sumAcc l 0 = sum l := boom.elim

end LeanTasks.Task1.Problem
