# Task 2 cases (sourced by scripts/mutate.sh).

mutant "task2: wrong definition (squares instead of cubes)" \
  "^error: .*Task2/Test\.lean" \
  "lake build" \
  "sed -i 's/sumCubes n + (n + 1) ^ 3$/sumCubes n + (n + 1) ^ 2/' LeanTasks/Task2/Defs.lean"

mutant "task2: reference solution proves a trivial statement" \
  "^error: .*Task2/Check\.lean.*Type mismatch" \
  "lake build" \
  "sed -i 's/^theorem sumCubes_eq (n : Nat) : sumCubes n = sumTo n ^ 2 := by$/theorem sumCubes_eq (n : Nat) : sumCubes n = sumCubes n := rfl\ntheorem sumCubes_eq_orig (n : Nat) : sumCubes n = sumTo n ^ 2 := by/' LeanTasks/Task2/Solution.lean"

mutant "task2: a disclosed shortcut in Calibration.lean stops working" \
  "^error: .*Task2/Calibration\.lean" \
  "lake build" \
  "sed -i 's/fun_induction sumCubes n <;> grind \[sumTo, Solution.two_mul_sumTo\]/fun_induction sumCubes n <;> grind [sumTo]/' LeanTasks/Task2/Calibration.lean"

grade_reject 2 "Gauss weakened to an inequality" \
  "^REJECT: statement of LeanTasks\.Task2\.Problem\.sumTo_eq differs" \
  "cp scripts/mutations/payloads/task2_weaker_gauss.lean \"\$SUB\""

grade_accept 2 "the automation shortcuts disclosed in Calibration.lean" \
  "cp scripts/mutations/payloads/task2_alt_solution.lean \"\$SUB\""
