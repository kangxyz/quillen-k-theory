/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/


import Mathlib.Init
import Mathlib.Tactic.Linter.TextBased

/-!
# Native text-style checks for the Quillen workspace

The pinned mathlib implementation checks source text without importing project
declarations. Module identities are resolved in each package, including the
independent downstream client. All supported native checks run without an
exception list or automatic source edits. Mathlib's legacy Python integration
requires its own scripts and is not called here.

Ordinary imports and declarations initialize the registry snapshot in the native
runtime, matching mathlib's executable driver.
-/


open Lean Lean.Linter Mathlib.Linter.TextBased

namespace QuillenTools

section LinterSetsSnapshot

instance {α : Type} [ToExpr α] : ToExpr (NameMap α) where
  toExpr entries := mkApp4 (.const ``Std.TreeMap.ofArray [.zero, .zero])
    (toTypeExpr Name) (toTypeExpr α) (toExpr entries.toArray)
    (.const ``Lean.Name.quickCmp [])
  toTypeExpr := .const ``LinterSets []

instance : ToExpr LinterSets := inferInstanceAs <| ToExpr (NameMap _)

/-- Snapshot the registered linter sets, as in the pinned mathlib style driver. -/
elab "quillen_linter_sets%" : term =>
  return toExpr <| (linterSetsExt.getState (← getEnv)).merged

end LinterSetsSnapshot

/-- Enable the standard set with its actual registry; omit unsupported Python tooling. -/
def nativeStyleOptions : LinterOptions := {
  toOptions := ({} : Options).setBool `linter.mathlibStandardSet true
    |>.setBool `linter.pythonStyle false
  linterSets := quillen_linter_sets%
}

/-- Run native text checks on the automatically enumerated workspace sources. -/
unsafe def lintStyleMain : IO UInt32 := do
  let inventory ← IO.Process.output {
    cmd := "python3"
    args := #["scripts/library_sources.py", "--style-sources", "--root", "."]
  }
  unless inventory.exitCode == 0 do
    IO.eprint inventory.stderr
    return inventory.exitCode
  let rows := inventory.stdout.splitOn "\n" |>.filter (· != "")
  if rows.isEmpty then
    throw <| IO.userError "No workspace sources found for text-style checking"
  let opts := nativeStyleOptions
  let mut modules : Array Name := #[]
  let mut paths : Array Name := #[]
  for row in rows do
    let [moduleName, path] := row.splitOn "\t"
      | throw <| IO.userError s!"Invalid source inventory row: {row}"
    modules := modules.push moduleName.toName
    unless path.endsWith ".lean" do
      throw <| IO.userError s!"Not a Lean source path: {path}"
    paths := paths.push <| (path.dropEnd 5).copy.splitOn "/" |>.foldl Name.str .anonymous
  let textErrors ← lintModules opts #[] paths .humanReadable false
  let nameErrors := (← modulesNotUpperCamelCase opts modules)
    + (← modulesOSForbidden opts modules)
  if textErrors != 0 || nameErrors != 0 then
    IO.eprintln "Native text-style checks failed"
    return 1
  IO.println s!"Native text-style checks passed for {rows.length} sources"
  return 0

end QuillenTools

/-- Lake executable entry point; imported initializers run before checking text. -/
unsafe def main : IO UInt32 := QuillenTools.lintStyleMain
