import Lean

/-!
# Axiom audit command

`#assert_standard_axioms foo` fails with an error unless the declaration `foo`
depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). In particular it rejects any proof that uses `sorry`
(`sorryAx`) or a user-declared `axiom`.
-/

open Lean Elab Command

/-- The axioms a reference solution is allowed to depend on. -/
def LeanTasks.standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_standard_axioms " id:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← collectAxioms c
  let bad := axs.filter (· ∉ LeanTasks.standardAxioms)
  unless bad.isEmpty do
    throwError "{c} depends on non-standard axioms: {bad.toList}"
