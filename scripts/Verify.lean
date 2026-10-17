import Lean

/-!
# Out-of-process verifier for a submitted solution

Usage, from the root of a *trusted* tree in which only
`LeanTasks/TaskN/Problem.olean` was produced from the submission
(`scripts/grade.sh` sets this up):

    lake env lean --run scripts/Verify.lean N

The submission is loaded as data with `importModules`. None of its syntax,
macros, instances or elaborators is run, so it cannot influence these checks.
(Checks written in a Lean file that imports the submission can be subverted,
e.g. by a macro that redefines the checking command.)

For every theorem name `thm` listed in `LeanTasks/TaskN/graded.txt`:

1. `LeanTasks.TaskN.Problem.thm` must be a theorem whose statement is the same
   kernel term (up to bound-variable names) as the statement of the reference
   `LeanTasks.TaskN.Solution.thm`.
2. Its proof may depend only on `propext`, `Classical.choice` and `Quot.sound`.
   The dependency closure is walked here, over the constants themselves.

The submission may import only `Init` and `LeanTasks.TaskN.Defs`. This is
checked from the header of its compiled file, before anything is loaded.

This program does not type-check proofs. `scripts/grade.sh` also runs
`leanchecker`, which replays every declaration of the submission through the
kernel.
-/

open Lean

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Constants that `ci` refers to directly. -/
def directDeps (ci : ConstantInfo) : Array Name := Id.run do
  let mut deps := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    deps := deps ++ v.getUsedConstants
  match ci with
  | .inductInfo iv => deps := deps ++ iv.ctors.toArray ++ iv.all.toArray
  | .ctorInfo cv => deps := deps.push cv.induct
  | .recInfo rv => deps := deps ++ rv.all.toArray ++ (rv.rules.toArray.flatMap (·.rhs.getUsedConstants))
  | _ => pure ()
  return deps

/-- Every axiom in the dependency closure of `root`. -/
def axiomsOf (env : Environment) (root : Name) : Except String (Array Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut axs : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => return .error s!"unknown constant {c}"
    | some ci =>
      if ci matches .axiomInfo _ then axs := axs.push c
      todo := todo ++ directDeps ci
  return .ok axs

def main (args : List String) : IO UInt32 := do
  let [task] := args
    | IO.eprintln "usage: lake env lean --run scripts/Verify.lean <task number>"; return 2
  let pre := s!"LeanTasks.Task{task}"
  let problem := s!"{pre}.Problem".toName
  let solution := s!"{pre}.Solution".toName
  let defs := s!"{pre}.Defs".toName
  let graded := (← IO.FS.lines s!"LeanTasks/Task{task}/graded.txt").toList.map
      (·.trimAscii.toString) |>.filter fun l => !l.isEmpty && !l.startsWith "#"
  if graded.isEmpty then
    IO.println s!"REJECT: no theorems listed in LeanTasks/Task{task}/graded.txt"; return 1
  initSearchPath (← findSysroot)
  -- Check the submission's header before loading anything.
  let (header, _) ← readModuleData (← findOLean problem)
  if header.isModule then
    IO.println s!"REJECT: {problem} uses the module system, which this grader does not support"
    return 1
  let badImports := header.imports.map (·.module) |>.filter (fun m => m != `Init && m != defs)
  unless badImports.isEmpty do
    for m in badImports do
      IO.println s!"REJECT: {problem} imports {m}; only Init and {defs} are allowed"
    return 1
  let env ← importModules #[{ module := problem }, { module := solution }] {}
  let mut ok := true
  let some idx := env.getModuleIdx? problem
    | IO.println s!"REJECT: module {problem} not found"; return 1
  -- Each graded theorem.
  for thm in graded do
    let p := problem ++ thm.toName
    let s := solution ++ thm.toName
    let some (.thmInfo si) := env.find? s
      | IO.println s!"REJECT: reference theorem {s} not found"; ok := false; continue
    let some pci := env.find? p
      | IO.println s!"REJECT: {p} is missing"; ok := false; continue
    let .thmInfo pi := pci
      | IO.println s!"REJECT: {p} is not a theorem"; ok := false; continue
    if env.getModuleIdxFor? p != some idx then
      IO.println s!"REJECT: {p} is not declared in {problem}"; ok := false
    unless pi.type == si.type && pi.levelParams == si.levelParams do
      IO.println s!"REJECT: statement of {p} differs from the reference statement"
      ok := false
    match axiomsOf env p with
    | .error e => IO.println s!"REJECT: {p}: {e}"; ok := false
    | .ok axs =>
      let bad := axs.filter (· ∉ standardAxioms)
      if bad.isEmpty then
        IO.println s!"ok: {p} (axioms: {axs.toList})"
      else
        IO.println s!"REJECT: {p} depends on non-standard axioms: {bad.toList}"
        ok := false
  IO.println (if ok then "verifier: all checks passed" else "REJECTED")
  return if ok then 0 else 1
