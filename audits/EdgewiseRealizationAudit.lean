import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.EdgewiseRealization

/-! Every declaration originating in the five edgewise/cofibration realization modules,
including private/generated declarations, is audited transitively. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Topology.Realization.MonomorphismHEP,
    `Quillen.Topology.Realization.Edgewise,
    `Quillen.Topology.Realization.EdgewiseCellular,
    `Quillen.Topology.Realization.EdgewiseSimplex,
    `Quillen.Topology.Realization.EdgewiseRealization]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count = 108 do throwError "Expected frozen 108-declaration scope; audited {count}"
  logInfo m!"Audited all {count} edgewise origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Edgewise.realizesEquiv_all
#print axioms Quillen.Edgewise.simplexContraction
#print axioms Quillen.Edgewise.contractibleSpace_simplex
#print axioms Quillen.Edgewise.realizesEquiv_endpoint
#print axioms Quillen.Edgewise.realizationHomotopyEquiv
#print axioms Quillen.Edgewise.realizationHomotopyEquiv_toFun
#print axioms Quillen.Edgewise.realizationHomotopyEquiv_naturality
#print axioms Quillen.Edgewise.realizationHomotopyEquiv_vertex
