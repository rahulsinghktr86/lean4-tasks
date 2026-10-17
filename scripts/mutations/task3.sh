# Task 3 cases (sourced by scripts/mutate.sh).

mutant "task3: wrong comparison in insertSorted" \
  "^error: .*Task3/Test\.lean" \
  "lake build" \
  "sed -i 's/if x ≤ y then/if x ≥ y then/' LeanTasks/Task3/Defs.lean"

mutant "task3: vacuous specification (every list is Sorted)" \
  "^error: .*Task3/Test\.lean" \
  "lake build" \
  "sed -i '/^  | cons (x y : Nat) (rest : List Nat)/a\\  | any (l : List Nat) : Sorted l' LeanTasks/Task3/Defs.lean"

mutant "task3: insertionSort drops elements" \
  "^error: .*Task3/Test\.lean" \
  "lake build" \
  "sed -i 's/| x :: xs => insertSorted x (insertionSort xs)/| _ :: xs => insertionSort xs/' LeanTasks/Task3/Defs.lean"

grade_reject 3 "uniqueness left as sorry" \
  "^REJECT: .*sorted_perm_unique depends on non-standard axioms: \[sorryAx\]" \
  "sed -e 's/LeanTasks\.Task3\.Solution/LeanTasks.Task3.Problem/g' \
       -e 's/^      rw \[ih (sorted_tail h₁) (sorted_tail h₂) ((List.perm_cons a).mp hp)\]$/      sorry/' \
       LeanTasks/Task3/Solution.lean > \"\$SUB\""

grade_accept 3 "a different solution, using core's List.Perm.eq_of_pairwise" \
  "cp scripts/mutations/payloads/task3_alt_solution.lean \"\$SUB\""
