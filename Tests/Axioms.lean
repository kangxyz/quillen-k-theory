import Quillen
import Lean.Util.CollectAxioms
/-! Audit every project-origin kernel declaration, including private helpers, and
every Quillen-namespaced declaration. Imported module name inventories avoid
forcing unrelated ConstantInfo values. The exact defining-origin predicate is
rechecked after deduplication, and local stage-2 declarations are included.
Transitive axiom collection and the allowed foundations are unchanged. -/

open Lean in
run_cmd do
  let env ← getEnv
  let selected (name : Name) : Bool :=
    let projectModule := match env.getModuleIdxFor? name with
      | some index => (`Quillen).isPrefixOf env.header.moduleNames[index.toNat]!
      | none => false
    projectModule || (`Quillen).isPrefixOf name
  let mut names : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let projectModule := (`Quillen).isPrefixOf env.header.moduleNames[i]!
    for name in env.header.moduleData[i]!.constNames do
      if projectModule || (`Quillen).isPrefixOf name then
        names := names.insert name
  names := env.constants.foldStage2 (fun names name _ =>
    if selected name then names.insert name else names) names
  let mut count : Nat := 0
  for name in names.toArray do
    if selected name then
      count := count + 1
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} project declarations (including private helpers): only standard Lean logical foundations."
