#!/usr/bin/env bash
# Grade a submitted solution of task N:
#
#   bash scripts/grade.sh N path/to/submitted/Problem.lean
#
# Exit status 0 means ACCEPT. The grade runs in two phases, so that nothing
# from the submission except its compiled .olean reaches the trusted tree:
#
#   1. Sandbox: a fresh copy of this repo, with the submission installed as
#      LeanTasks/TaskN/Problem.lean, builds the submission (and nothing else).
#   2. Trusted tree: a second fresh copy, created only after phase 1 has
#      finished, builds Defs and the reference Solution from pristine sources.
#      The submission's Problem.olean is copied in, and then
#        - scripts/Verify.lean loads the submission as data and checks
#          imports, statements and axioms (see that file), and
#        - `leanchecker` replays every declaration of the submission through
#          the kernel.
#
# Threat model: Lean code can run arbitrary IO while it is being compiled, and
# phase 1 runs it with your permissions. The two phases stop a submission from
# tampering with the files used for grading, but not with the rest of your
# machine. Loading a compiled file is also not hardened against a maliciously
# crafted .olean. Grade untrusted submissions inside a disposable container or VM.
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: bash scripts/grade.sh <task number> <submitted Problem.lean>" >&2
  exit 2
fi
task="$1"
submission="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
root="$(cd "$(dirname "$0")/.." && pwd)"
module="LeanTasks.Task${task}.Problem"
olean_dir=".lake/build/lib/lean/LeanTasks/Task${task}"

if [ ! -f "$root/LeanTasks/Task${task}/graded.txt" ]; then
  echo "REJECT: there is no task ${task}" >&2
  exit 2
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Snapshot of the pristine sources (no build outputs, no git metadata).
(cd "$root" && tar --exclude=.git --exclude=.lake -cf - .) > "$tmp/snapshot.tar"
snapshot_sum="$(sha256sum < "$tmp/snapshot.tar")"

echo "== phase 1: building the submission in a sandbox copy"
mkdir "$tmp/sandbox"
tar -xf "$tmp/snapshot.tar" -C "$tmp/sandbox"
cp "$submission" "$tmp/sandbox/LeanTasks/Task${task}/Problem.lean"
if ! (cd "$tmp/sandbox" && lake build "$module"); then
  echo "REJECT: the submission does not compile"
  exit 1
fi
cp "$tmp/sandbox/$olean_dir/Problem.olean" "$tmp/submission.olean"

echo "== phase 2: checking the submission against pristine sources"
if [ "$(sha256sum < "$tmp/snapshot.tar")" != "$snapshot_sum" ]; then
  echo "REJECT: the pristine snapshot was modified during phase 1"
  exit 1
fi
mkdir "$tmp/trusted"
tar -xf "$tmp/snapshot.tar" -C "$tmp/trusted"
cd "$tmp/trusted"
lake build "LeanTasks.Task${task}.Defs" "LeanTasks.Task${task}.Solution"
cp "$tmp/submission.olean" "$olean_dir/Problem.olean"

if ! lake env lean --run scripts/Verify.lean "$task"; then
  exit 1
fi
if ! lake env leanchecker "$module"; then
  echo "REJECT: leanchecker (kernel re-check) failed"
  exit 1
fi
echo "ACCEPT"
