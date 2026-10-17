# Lean 4 tasks

[![Lean build & checks](https://github.com/rahulsinghktr86/lean4-tasks/actions/workflows/ci.yml/badge.svg)](https://github.com/rahulsinghktr86/lean4-tasks/actions/workflows/ci.yml)

Four self-contained Lean 4 proof tasks. Each one has a problem statement with
`sorry`, a fully checked reference solution, unit tests for its definitions,
and a machine-checked calibration of its difficulty. Submissions are graded by
an out-of-process verifier. Each task is submitted for review as its own pull
request.

* **Lean:** `leanprover/lean4:v4.34.1` (pinned in [`lean-toolchain`](lean-toolchain))
* **Mathlib:** **not allowed** for any task. Statements and solutions use only
  core Lean 4, so the project builds in seconds with no external dependencies.
  Core tactics such as `omega`, `simp`, `grind` and `lia` are allowed.

## Tasks

| # | Task | Difficulty | Theorems | PR |
|---|------|------------|----------|----|
| 1 | Tail-recursive sum is correct | easy | `sumAcc l 0 = sum l` | [#1](https://github.com/rahulsinghktr86/lean4-tasks/pull/1) |
| 2 | Gauss's formula and Nicomachus's theorem | easy | `sumTo n = n * (n + 1) / 2`, `sumCubes n = sumTo n ^ 2` | [#2](https://github.com/rahulsinghktr86/lean4-tasks/pull/2) |
| 3 | Insertion sort is correct; sorted output is unique | easy–medium | sorted, permutation, uniqueness of sorted permutations, invariance under reordering | [#3](https://github.com/rahulsinghktr86/lean4-tasks/pull/3) |
| 4 | A verified compiler: correct and injective | medium | `exec env (compile e) s = some (eval env e :: s)`, `Function.Injective compile` | [#4](https://github.com/rahulsinghktr86/lean4-tasks/pull/4) |

Difficulty ratings take core automation into account. Each task's
`Calibration.lean` checks, in Lean, that the obvious automated attempts fail,
and also records any automation shortcuts that do work, so the ratings can be
verified rather than taken on trust.

## Layout

```
LeanTasks/
  AxiomCheck.lean        `#assert_standard_axioms`, an in-Lean axiom audit
  AxiomCheckTest.lean    self-test: the audit rejects sorry, axioms, native_decide
  TaskN/
    Defs.lean            definitions shared by problem and solution (fixed)
    Problem.lean         the task: statement(s) with `sorry`, description, hints
    Solution.lean        reference solution, no `sorry`
    Test.lean            unit tests for Defs.lean (imports only Defs.lean)
    Check.lean           the published statements match the reference; the
                         reference uses only standard axioms
    Calibration.lean     machine-checked evidence for the difficulty rating
    graded.txt           the theorems the grader checks
scripts/
  Verify.lean            out-of-process verifier (statements, axioms, imports)
  grade.sh               two-phase grader: grade.sh N path/to/Problem.lean
  grade-reference.sh     tests the grader on each task's own files
  mutate.sh              mutation tests (cases in scripts/mutations/)
```

Definitions sit in their own `Defs.lean` so the problem and the solution use the
*same* constants. A solution cannot quietly redefine `sum` to make its proof
easier.

## Solving a task

Edit `LeanTasks/TaskN/Problem.lean` and replace each `sorry` with a proof.
Rules:

* do not change the theorem statements or `Defs.lean`;
* helper lemmas and helper definitions are allowed;
* `Problem.lean` may import only `LeanTasks.TaskN.Defs` (core Lean is always
  available); Mathlib is not allowed.

`lake build` gives quick feedback while you work (for instance, `Check.lean`
reports a changed statement), but it is not the grader.

## Grading a submission

```sh
bash scripts/grade.sh N path/to/Problem.lean   # exit status 0 = ACCEPT
```

The grader works in two phases, so that nothing from the submission except its
compiled `.olean` reaches the trusted files:

1. **Sandbox.** A fresh copy of the repo, with the submission installed as
   `LeanTasks/TaskN/Problem.lean`, compiles the submission.
2. **Trusted tree.** A second fresh copy, created only after phase 1 has
   finished, compiles `Defs.lean` and the reference `Solution.lean` from
   pristine sources and takes in only the submission's `Problem.olean`. Then:
   * **`leanchecker`** replays every declaration of the submission through the
     kernel, so a proof cannot sneak past the kernel (for example by adding
     declarations with kernel checking disabled);
   * **[`scripts/Verify.lean`](scripts/Verify.lean)** loads the submission *as
     data* and, for each theorem in `graded.txt`, requires the statement to be
     the same kernel term as the reference statement, and the proof to depend
     only on `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, no
     custom `axiom`, no `native_decide`). It also requires `Problem.lean` to
     import nothing but `Defs.lean`.

Why out of process: a check written as Lean code in a file that imports the
submission can be subverted by that submission, for example by a macro that
redefines the checking command, a decoy constant that a name resolves to, or a
coercion. The verifier never runs any of the submission's syntax, macros,
instances or elaborators.

**Threat model.** Lean code can run arbitrary IO while it is being compiled, and
phase 1 compiles the submission with your permissions. The two phases stop a
submission from tampering with the files used for grading (the mutation tests
include a submission that tries), but not with the rest of your machine. Grade
untrusted submissions inside a disposable container or VM.

## How the repository is tested

`lake build` fails unless:

1. **Unit tests** (`TaskN/Test.lean`) pass. They are kernel-checked
   (`decide` / `rfl`), include negative tests (e.g. `¬ Sorted [2, 1]`), and pin
   every defining equation, so a definition cannot be replaced by one that makes
   a theorem trivial. They import only `Defs.lean`, so they run even when a
   proof elsewhere breaks.
2. **Consistency checks** (`TaskN/Check.lean`) pass: each published statement is
   the statement the reference proves, and the reference uses only standard
   axioms.
3. **Calibration** (`TaskN/Calibration.lean`) holds: each claimed automation
   failure really fails, and each disclosed shortcut really works.
4. **Audit self-test** (`AxiomCheckTest.lean`) passes.

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) also:

* re-checks every module with `leanchecker`;
* greps the reference solutions for `sorry`;
* **tests the grader** (`scripts/grade-reference.sh`): each reference solution,
  submitted as a solver's `Problem.lean`, must be accepted, and each unsolved
  `Problem.lean` must be rejected *only* because of `sorry`. The second check
  also confirms, through the grader's own statement comparison, that the
  published statements are exactly the reference statements;
* runs the **mutation tests** (`scripts/mutate.sh`). Each case breaks something
  on purpose and checks that the right check catches it, with the expected
  error:
  * wrong or vacuous definitions, `sorry` in a reference proof, a published
    statement that differs from the reference, a broken calibration claim;
  * cheating submissions: `sorry` (also hidden in a helper lemma), weakened
    statements, statements replaced by `True` together with a decoy constant, a
    coercion, a `type_of%` macro or a decoy axiom, a macro that disables the
    in-Lean audit, re-exporting the reference solution, a custom axiom,
    `native_decide` with `implemented_by`, a proof of `False` added with kernel
    checking disabled, and a submission that overwrites the grader while it is
    being compiled;
  * correct submissions that differ from the reference, which must be accepted;
  * weakened graders (verifier without the axiom check, the statement
    comparison or the import restriction; no `leanchecker`; submission built
    and checked in one tree). Each must then accept some bad submission, which
    shows that every part of the grader is needed.

Before running any case, `mutate.sh` checks that the unmutated repo builds and
that every reference solution is accepted, so a broken environment cannot make
a case pass.

## Building locally

```sh
# requires elan: https://github.com/leanprover/elan
lake build
bash scripts/grade-reference.sh   # test the grader on every task
bash scripts/mutate.sh            # mutation tests (several minutes)
```

The only expected warnings are ``declaration uses `sorry` `` in the
`Problem.lean` files.

## Authorship

These tasks, their reference solutions and the checking infrastructure were
written with the assistance of Claude (Anthropic's AI model). Commits are
co-authored accordingly.
