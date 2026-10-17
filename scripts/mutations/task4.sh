# Task 4 cases (sourced by scripts/mutate.sh).

mutant "task4: machine computes b - a instead of a - b" \
  "^error: .*Task4/Test\.lean" \
  "lake build" \
  "sed -i 's/exec env p ((a - b) :: s)/exec env p ((b - a) :: s)/' LeanTasks/Task4/Defs.lean"

mutant "task4: compiler emits sub operands in the wrong order" \
  "^error: .*Task4/Test\.lean" \
  "lake build" \
  "sed -i 's/| .sub a b => compile a ++ compile b ++ \[.sub\]/| .sub a b => compile b ++ compile a ++ [.sub]/' LeanTasks/Task4/Defs.lean"

# Changes eval and exec consistently, so every reference proof still compiles;
# only the unit tests can catch it.
mutant "task4: multiplication taken mod 1000 in both eval and exec" \
  "^error: .*Task4/Test\.lean" \
  "lake build" \
  "sed -i -e 's/| .mul a b => eval env a \* eval env b$/| .mul a b => eval env a * eval env b % 1000/' \
          -e 's/exec env p ((a \* b) :: s)$/exec env p ((a * b % 1000) :: s)/' LeanTasks/Task4/Defs.lean"

mutant "task4: injectivity reference proof replaced by sorry" \
  "^error: .*Task4/Check\.lean.*sorryAx" \
  "lake build" \
  "sed -i 's/^  simpa using h₁.symm$/  sorry/' LeanTasks/Task4/Solution.lean"

grade_reject 4 "statements replaced by True, plus decoy constants" \
  "^REJECT: statement of LeanTasks\.Task4\.Problem\.compile_injective differs" \
  "cp scripts/mutations/payloads/task4_true_with_decoy.lean \"\$SUB\""

grade_accept 4 "a different proof, via exec on appended programs" \
  "cp scripts/mutations/payloads/task4_alt_solution.lean \"\$SUB\""
