import Quillen.Resolution.Theorem
import Lean.Util.CollectAxioms

/-! Audit every declaration originating in the canonical resolution modules. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let isResolutionModule := match env.getModuleIdxFor? name with
      | some index => (`Quillen.Resolution).isPrefixOf env.header.moduleNames[index.toNat]!
      | none => false
    if isResolutionModule then
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} resolution declarations: only propext, Classical.choice, and Quot.sound."

#print axioms Quillen.Resolution.classifyingHomotopyEquiv
#print axioms Quillen.Resolution.classifyingHomotopyEquiv_toFun
#print axioms Quillen.Resolution.inclusionKMap_bijective
#print axioms Quillen.Resolution.KEquiv
#print axioms Quillen.Resolution.KEquiv_toMonoidHom
#print axioms Quillen.Resolution.stratumNerveCocone_isColimit
#print axioms Quillen.ExactStructure.resolutionLength_resolving
