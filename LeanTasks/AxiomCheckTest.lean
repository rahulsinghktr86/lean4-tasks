import LeanTasks.AxiomCheck

/-!
# Self-test for `#assert_standard_axioms`

Shows that the audit accepts proofs that use the standard axioms and rejects
`sorry`, user-declared axioms and `native_decide`. If any rejection stopped
happening, the `#guard_msgs` below would fail the build.
-/

namespace LeanTasks.AxiomCheckTest

/-! Accepted: no axioms, and the standard axioms. -/

theorem noAxioms : 2 + 2 = 4 := rfl
#assert_standard_axioms LeanTasks.AxiomCheckTest.noAxioms

theorem usesChoice (p : Prop) : p ∨ ¬p := Classical.em p
#assert_standard_axioms LeanTasks.AxiomCheckTest.usesChoice

/-! Rejected: `sorry`. -/

set_option warn.sorry false in
theorem usesSorry : 2 + 2 = 5 := sorry

/--
error: LeanTasks.AxiomCheckTest.usesSorry depends on non-standard axioms: [sorryAx]
-/
#guard_msgs in #assert_standard_axioms LeanTasks.AxiomCheckTest.usesSorry

/-! Rejected: a user-declared axiom. -/

axiom cheat : 2 + 2 = 5
theorem usesAxiom : 2 + 2 = 5 := cheat

/--
error: LeanTasks.AxiomCheckTest.usesAxiom depends on non-standard axioms: [LeanTasks.AxiomCheckTest.cheat]
-/
#guard_msgs in #assert_standard_axioms LeanTasks.AxiomCheckTest.usesAxiom

/-! Rejected: `native_decide`, which trusts the compiler instead of the kernel. -/

theorem usesNativeDecide : 2 + 2 = 4 := by native_decide

/--
error: LeanTasks.AxiomCheckTest.usesNativeDecide depends on non-standard axioms: [LeanTasks.AxiomCheckTest.usesNativeDecide._native.native_decide.ax_1_1]
-/
#guard_msgs in #assert_standard_axioms LeanTasks.AxiomCheckTest.usesNativeDecide

end LeanTasks.AxiomCheckTest
