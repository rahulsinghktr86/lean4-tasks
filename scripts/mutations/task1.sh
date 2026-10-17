# Task 1 cases (sourced by scripts/mutate.sh). Task 1 also carries the tests of
# the grader itself, because they need at least one task.

## The repository's own checks

mutant "task1: reference proof replaced by sorry" \
  "^error: .*Task1/Check\.lean.*sorryAx" \
  "lake build" \
  "sed -i 's/^  simp \[sumAcc_eq\]$/  sorry/' LeanTasks/Task1/Solution.lean"

mutant "task1: wrong definition (accumulator off by one)" \
  "^error: .*Task1/Test\.lean" \
  "lake build" \
  "sed -i 's/sumAcc xs (acc + x)$/sumAcc xs (acc + x + 1)/' LeanTasks/Task1/Defs.lean"

mutant "task1: published statement differs from the reference" \
  "^error: .*Task1/Check\.lean.*Type mismatch" \
  "lake build" \
  "sed -i 's/sumAcc l 0 = sum l := by/sumAcc l 0 = sumAcc l 0 := by/' LeanTasks/Task1/Problem.lean"

## Bad submissions

grade_reject 1 "the unsolved problem (sorry)" \
  "^REJECT: .*sorryAx" \
  "cp LeanTasks/Task1/Problem.lean \"\$SUB\""

grade_reject 1 "sorry hidden in a helper lemma" \
  "^REJECT: .*sorryAx" \
  "cp scripts/mutations/payloads/task1_helper_sorry.lean \"\$SUB\""

grade_reject 1 "weakened statement" \
  "^REJECT: statement of .* differs" \
  "sed -e 's/LeanTasks\.Task1\.Solution/LeanTasks.Task1.Problem/g' \
       -e 's/sumAcc l 0 = sum l := by/sumAcc l 0 = sumAcc l 0 := by/' \
       LeanTasks/Task1/Solution.lean > \"\$SUB\""

grade_reject 1 "statement replaced by True, plus a decoy constant" \
  "^REJECT: statement of .* differs" \
  "cp scripts/mutations/payloads/task1_true_with_decoy.lean \"\$SUB\""

grade_reject 1 "statement replaced by True, plus a coercion" \
  "^REJECT: statement of .* differs" \
  "cp scripts/mutations/payloads/task1_coe.lean \"\$SUB\""

grade_reject 1 "statement replaced by True, plus a macro rewriting type_of%" \
  "^REJECT: statement of .* differs" \
  "cp scripts/mutations/payloads/task1_macro_typeof.lean \"\$SUB\""

grade_reject 1 "statement replaced by True, plus a decoy axiom" \
  "^REJECT: statement of .* differs" \
  "cp scripts/mutations/payloads/task1_decoy_axiom.lean \"\$SUB\""

grade_reject 1 "macro that disables the in-Lean axiom audit, with sorry" \
  "^REJECT: .* imports LeanTasks\.AxiomCheck;" \
  "cp scripts/mutations/payloads/task1_macro_audit.lean \"\$SUB\""

grade_reject 1 "re-exports the reference solution" \
  "^REJECT: .* imports LeanTasks\.Task1\.Solution;" \
  "cp scripts/mutations/payloads/task1_import_solution.lean \"\$SUB\""

grade_reject 1 "custom axiom" \
  "^REJECT: .*non-standard axioms: \[LeanTasks\.Task1\.Problem\.cheat\]" \
  "cp scripts/mutations/payloads/task1_custom_axiom.lean \"\$SUB\""

grade_reject 1 "native_decide with implemented_by" \
  "^REJECT: .*non-standard axioms: .*native_decide" \
  "cp scripts/mutations/payloads/task1_native_decide.lean \"\$SUB\""

# This payload needs `import Lean`, so the import restriction rejects it. The
# grader tests below show that leanchecker also rejects it on its own.
grade_reject 1 "proof of False added with kernel checking disabled" \
  "^REJECT: .* imports Lean;" \
  "cp scripts/mutations/payloads/task1_kernel_bypass.lean \"\$SUB\""

grade_reject 1 "overwrites the grader while being compiled, with sorry" \
  "^REJECT: .*sorryAx" \
  "cp scripts/mutations/payloads/task1_build_time_io.lean \"\$SUB\""

grade_reject 1 "replaces the pristine snapshot while being compiled, with sorry" \
  "^REJECT: the pristine snapshot was modified" \
  "cp scripts/mutations/payloads/task1_snapshot_tamper.lean \"\$SUB\""

## A correct submission that differs from the reference

grade_accept 1 "alternative proof" \
  "cp scripts/mutations/payloads/task1_alt_solution.lean \"\$SUB\""

## Weakened graders
# Each `mutant` below removes part of the grader and shows that the weakened
# grader then ACCEPTS a bad submission, so that part is needed. The `defense`
# case shows that leanchecker is an independent second line of defense against
# the kernel bypass, which the import restriction already stops.

mutant "grader: Verify.lean ignores axioms" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 LeanTasks/Task1/Problem.lean" \
  "sed -i 's/if bad.isEmpty then/if true then/' scripts/Verify.lean"

mutant "grader: Verify.lean skips the statement comparison" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 scripts/mutations/payloads/task1_true_with_decoy.lean" \
  "sed -i 's/unless pi.type == si.type && pi.levelParams == si.levelParams do/unless true do/' scripts/Verify.lean"

mutant "grader: Verify.lean allows any import" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 scripts/mutations/payloads/task1_import_solution.lean" \
  "sed -i 's/(fun m => m != .Init && m != defs)/(fun _ => false)/' scripts/Verify.lean"

defense "grader: with imports unrestricted, leanchecker alone rejects the kernel bypass" \
  "^REJECT: leanchecker" \
  "sed -i 's/(fun m => m != .Init && m != defs)/(fun _ => false)/' scripts/Verify.lean" \
  1 scripts/mutations/payloads/task1_kernel_bypass.lean

mutant "grader: grade.sh skips leanchecker (and imports are unrestricted)" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 scripts/mutations/payloads/task1_kernel_bypass.lean" \
  "sed -i 's/^if ! lake env leanchecker \"\$module\"; then$/if false; then/' scripts/grade.sh && \
   sed -i 's/(fun m => m != .Init && m != defs)/(fun _ => false)/' scripts/Verify.lean"

mutant "grader: grade.sh skips the snapshot integrity check" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 scripts/mutations/payloads/task1_snapshot_tamper.lean" \
  "sed -i 's/snapshot_sum\" ]; then/snapshot_sum\" ] \\&\\& false; then/' scripts/grade.sh"

mutant "grader: grade.sh builds and checks the submission in one tree" \
  "^ACCEPT$" \
  "! bash scripts/grade.sh 1 scripts/mutations/payloads/task1_build_time_io.lean" \
  "sed -i 's/^cd \"\$tmp\/trusted\"$/cd \"\$tmp\/sandbox\"/' scripts/grade.sh"
