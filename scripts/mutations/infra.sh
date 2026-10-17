# Mutations of the shared infrastructure (sourced by scripts/mutate.sh).

mutant "infra: the in-Lean axiom audit accepts everything" \
  "^error: .*AxiomCheckTest\.lean" \
  "lake build" \
  "sed -i 's/unless bad.isEmpty do/unless true do/' LeanTasks/AxiomCheck.lean"
