/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.TextBased

/-!
# Environment lint for selected defining modules

Run `lake build MODULE...` first, then
`lake env lean --run Tools/LintScoped.lean MODULE...`.

The runner uses CI's default Batteries linters, including slow checks, and native text checks.
It selects declarations by their exact defining modules, including generated declarations.
Dependencies are loaded for elaboration but their declarations are outside the selected scope.
Run this command from the repository root with local defining modules. It reads existing
artifacts and never starts a build or changes linter exclusions.
-/

open Lean Core Batteries.Tactic.Lint

namespace QuillenTools.ScopedLint

/-- Read the existing CI exclusions without creating or updating them. -/
def readExclusions : IO (Array (Name × Name)) := do
  let path : System.FilePath := "scripts/nolints.json"
  unless ← path.pathExists do
    return #[]
  let json ← IO.FS.readFile path
  let parsed ← IO.ofExcept (Json.parse json)
  IO.ofExcept (fromJson? parsed)

/-- Apply CI's default environment and native text checks to the named defining modules. -/
unsafe def run (modules : Array Name) : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let imports : Array Import := (modules.push `Batteries.Tactic.Lint
    |>.push `Mathlib.Tactic.Linter.TextBased).map fun name =>
    { module := name }
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
  let exclusions ← readExclusions
  let ctx : Core.Context := { fileName := "", fileMap := default, options := {} }
  let state : Core.State := { env }
  let action : CoreM Unit := do
    let decls := (← getAllDecls).filter fun name =>
      match env.getModuleIdxFor? name with
      | some index => modules.contains env.header.moduleNames[index.toNat]!
      | none => false
    if decls.isEmpty then
      throwError "Selected modules define no declarations; specify defining leaf modules"
    let linters ← getChecks (slow := true) (runOnly := none) (runAlways := none)
    let results ← lintCore decls linters (inIO := true)
    let results := results.map fun (linter, failures) =>
      (linter, exclusions.foldl (init := failures) fun failures (name, decl) =>
        if name == linter.name then failures.erase decl else failures)
    if results.any (!·.2.isEmpty) then
      let message ← formatLinterResults results decls
        (groupByFilename := true) (useErrorFormat := true)
        "in selected defining modules" (runSlowLinters := true) .medium linters.size
      throwError "{message}"
    IO.println s!"Scoped environment lint passed: {modules.size} modules, \
      {decls.size} declarations, {linters.size} linters."
  _ ← CoreM.toIO action ctx state
  let styleOptions : Lean.Linter.LinterOptions := {
    toOptions := ({} : Options).setBool `linter.mathlibStandardSet true
      |>.setBool `linter.pythonStyle false
    linterSets := (Lean.Linter.linterSetsExt.getState env).merged
  }
  let textErrors ← Mathlib.Linter.TextBased.lintModules styleOptions #[] modules
    .humanReadable false
  let nameErrors := (← Mathlib.Linter.TextBased.modulesNotUpperCamelCase styleOptions modules)
    + (← Mathlib.Linter.TextBased.modulesOSForbidden styleOptions modules)
  if textErrors != 0 || nameErrors != 0 then
    throw <| IO.userError "Scoped native text lint failed"
  IO.println s!"Scoped native text lint passed: {modules.size} modules."

end QuillenTools.ScopedLint

/-- Run scoped lint for explicitly named modules, using existing compiled artifacts. -/
unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lake env lean --run Tools/LintScoped.lean MODULE..."
    return 2
  if args == ["--help"] then
    IO.println "Usage: lake env lean --run Tools/LintScoped.lean MODULE..."
    return 0
  try
    QuillenTools.ScopedLint.run (args.map String.toName).toArray
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
