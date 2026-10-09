import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.EdgewiseBisimplicial

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Topology.Realization.EdgewiseBisimplicial do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}: {axioms}"
  unless count > 0 do throwError "No bisimplicial edgewise declarations imported"
  logInfo m!"Audited all {count} bisimplicial edgewise declarations, including private/generated declarations."

#print axioms Quillen.Edgewise.verticalRealizationHomotopyEquiv
#print axioms Quillen.Edgewise.horizontalRealizationHomotopyEquiv
#print axioms Quillen.Edgewise.upperIndexRealizationHomotopyEquiv
