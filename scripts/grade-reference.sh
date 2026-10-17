#!/usr/bin/env bash
# Test the grader (scripts/grade.sh) on the tasks' own files. For each task N:
#
#   1. The reference solution, submitted as LeanTasks/TaskN/Problem.lean with
#      its namespace renamed, must be ACCEPTED.
#   2. The unsolved LeanTasks/TaskN/Problem.lean must be REJECTED, and only
#      because it uses `sorry`. This also confirms, through the grader's own
#      statement comparison, that the published statements are exactly the
#      reference statements.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

found=0
for sol in "$root"/LeanTasks/Task*/Solution.lean; do
  [ -e "$sol" ] || continue
  found=1
  dir="$(dirname "$sol")"
  n="${dir##*/Task}"

  echo "== task ${n}: the reference solution must be accepted"
  sed "s/LeanTasks\.Task${n}\.Solution/LeanTasks.Task${n}.Problem/g" "$sol" > "$tmp/ref${n}.lean"
  if ! out="$(bash "$root/scripts/grade.sh" "$n" "$tmp/ref${n}.lean" 2>&1)"; then
    echo "$out"
    echo "FAIL: the reference solution of task ${n} was rejected"
    exit 1
  fi
  grep -E "^(ok|ACCEPT)" <<<"$out"

  echo "== task ${n}: the unsolved problem must be rejected, only for sorry"
  if out="$(bash "$root/scripts/grade.sh" "$n" "$dir/Problem.lean" 2>&1)"; then
    echo "$out"
    echo "FAIL: the unsolved problem of task ${n} was accepted"
    exit 1
  fi
  rejects="$(grep "^REJECT:" <<<"$out" || true)"
  expected="$(grep -c . "$dir/graded.txt")"
  if [ "$(grep -c "non-standard axioms: \[sorryAx\]$" <<<"$rejects")" != "$expected" ] \
     || [ "$(grep -c . <<<"$rejects")" != "$expected" ]; then
    echo "$out"
    echo "FAIL: task ${n} was rejected for an unexpected reason"
    exit 1
  fi
  echo "$rejects"
done

if [ "$found" -eq 0 ]; then
  echo "No tasks found; nothing to grade."
fi
