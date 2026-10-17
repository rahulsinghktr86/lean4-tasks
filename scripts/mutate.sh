#!/usr/bin/env bash
# Mutation tests: show that the checks and the grader catch what they claim to.
#
# The cases are defined in scripts/mutations/*.sh, using three functions:
#
#   mutant <description> <expected regex> <check command> <shell code>
#       The shell code breaks a copy of the repo, e.g. a wrong definition, a
#       `sorry` in a reference proof, or a weakened grader. The check command
#       must pass on the unmutated copy and FAIL on the mutated one, with
#       output matching the regex, so we know *which* check caught it.
#
#   grade_reject <task> <description> <expected regex> <shell code>
#       The shell code writes a bad submission to "$SUB", e.g. a changed
#       statement, a custom axiom, or a macro that disables a check.
#       scripts/grade.sh must REJECT it, with output matching the regex.
#
#   grade_accept <task> <description> <shell code>
#       The shell code writes a correct solution, different from the reference
#       one, to "$SUB". scripts/grade.sh must ACCEPT it.
#
#   defense <description> <expected regex> <shell code> <task> <submission>
#       The shell code weakens the grader in a copy of the repo (e.g. removes
#       one check). The weakened grader must still REJECT the submission, with
#       output matching the regex: another check takes over.
#
# Shell code runs in the repo root; it must only read there (it may write to
# "$SUB"). Before any case runs, the unmutated repo must build and the grader
# must accept every reference solution, so a broken environment cannot make a
# mutant look "killed".
set -uo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
total=0
failed=0

fail() {
  echo "FAILED:   $1"
  failed=$((failed + 1))
}

# Lake's `trace:` lines echo file paths, so they are ignored when matching.
# (No pipes here: with `pipefail`, a reader that stops early, like `grep -q`,
# would make the whole pipeline fail on long output.)
untraced() { grep -v '^trace:' <<<"$1" || true; }
matches() {
  local text
  text="$(untraced "$2")"
  grep -qE -- "$1" <<<"$text"
}

# Prints the first non-trace line of $2 that matches regex $1, indented.
show() {
  local text line
  text="$(untraced "$2")"
  line="$(grep -m1 -E -- "$1" <<<"$text" || true)"
  [ -n "$line" ] && echo "          $line"
  return 0
}

echo "== baseline"
mkdir "$tmp/base"
(cd "$root" && tar --exclude=.git -cf - .) | tar -xf - -C "$tmp/base"
if ! (cd "$tmp/base" && lake build >/dev/null 2>&1); then
  echo "baseline failed: lake build does not pass on the unmutated repo"
  exit 1
fi
if ! bash "$tmp/base/scripts/grade-reference.sh" >/dev/null 2>&1; then
  echo "baseline failed: scripts/grade-reference.sh does not pass on the unmutated repo"
  exit 1
fi
echo "ok"
echo "== mutants"

mutant() {
  local desc="$1" expect="$2" check="$3" code="$4" m="$tmp/mutant" out
  total=$((total + 1))
  if ! out="$(cd "$tmp/base" && eval "$check" 2>&1)"; then
    fail "$desc (the check fails even without the mutation)"
    return
  fi
  rm -rf "$m"
  cp -r "$tmp/base" "$m"
  if ! (cd "$m" && eval "$code"); then
    fail "$desc (the mutation could not be applied)"
    return
  fi
  if diff -rq --exclude=.lake "$tmp/base" "$m" >/dev/null; then
    fail "$desc (the mutation changed nothing)"
    return
  fi
  if out="$(cd "$m" && eval "$check" 2>&1)"; then
    fail "$desc (the check still passes)"
    return
  fi
  if ! matches "$expect" "$out"; then
    fail "$desc (the check failed, but its output does not match /$expect/)"
    show "error|REJECT" "$out"
    return
  fi
  echo "killed:   $desc"
  show "$expect" "$out"
}

# Writes a submission for task $1 into $SUB by running shell code $2 in the
# repo root. Fails if the submission is empty or identical to the reference.
make_submission() {
  local task="$1" code="$2"
  SUB="$tmp/submission.lean"
  rm -f "$SUB"
  sed "s/LeanTasks\.Task${task}\.Solution/LeanTasks.Task${task}.Problem/g" \
    "$root/LeanTasks/Task${task}/Solution.lean" > "$tmp/reference.lean"
  (cd "$root" && export SUB && eval "$code") || return 1
  [ -s "$SUB" ] && ! cmp -s "$SUB" "$tmp/reference.lean"
}

grade_reject() {
  local task="$1" desc="task${1}: grader rejects: $2" expect="$3" code="$4" out
  total=$((total + 1))
  if ! make_submission "$task" "$code"; then
    fail "$desc (could not create a submission that differs from the reference)"
    return
  fi
  if out="$(bash "$root/scripts/grade.sh" "$task" "$SUB" 2>&1)"; then
    fail "$desc (the grader ACCEPTED it)"
    return
  fi
  if ! matches "$expect" "$out"; then
    fail "$desc (rejected, but the output does not match /$expect/)"
    show "error|REJECT" "$out"
    return
  fi
  echo "rejected: $desc"
  show "$expect" "$out"
}

grade_accept() {
  local task="$1" desc="task${1}: grader accepts: $2" code="$3" out
  total=$((total + 1))
  if ! make_submission "$task" "$code"; then
    fail "$desc (could not create a submission that differs from the reference)"
    return
  fi
  if ! out="$(bash "$root/scripts/grade.sh" "$task" "$SUB" 2>&1)"; then
    fail "$desc (the grader REJECTED it)"
    show "error|REJECT" "$out"
    return
  fi
  echo "accepted: $desc"
}

defense() {
  local desc="$1" expect="$2" code="$3" task="$4" sub="$5" m="$tmp/mutant" out
  total=$((total + 1))
  rm -rf "$m"
  cp -r "$tmp/base" "$m"
  if ! (cd "$m" && eval "$code"); then
    fail "$desc (the change could not be applied)"
    return
  fi
  if diff -rq --exclude=.lake "$tmp/base" "$m" >/dev/null; then
    fail "$desc (the change changed nothing)"
    return
  fi
  if out="$(cd "$m" && bash scripts/grade.sh "$task" "$sub" 2>&1)"; then
    fail "$desc (the weakened grader ACCEPTED it)"
    return
  fi
  if ! matches "$expect" "$out"; then
    fail "$desc (rejected, but the output does not match /$expect/)"
    show "error|REJECT" "$out"
    return
  fi
  echo "rejected: $desc"
  show "$expect" "$out"
}

shopt -s nullglob
for f in "$root"/scripts/mutations/*.sh; do
  # shellcheck source=/dev/null
  source "$f"
done

echo "$((total - failed))/$total cases behaved as expected"
[ "$failed" -eq 0 ]
