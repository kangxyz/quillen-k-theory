import Quillen
import Lean.Util.CollectAxioms
/-! Fail if any declaration in the project's modules (including private helpers) depends on a proof
placeholder or an assumption beyond Lean's standard logical foundations. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let projectModule := match env.getModuleIdxFor? name with
      | some index => (`Quillen).isPrefixOf env.header.moduleNames[index.toNat]!
      | none => false
    if projectModule || (`Quillen).isPrefixOf name then
      count := count + 1
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} project declarations (including private helpers): only standard Lean logical foundations."
