import Lean.Util.CollectAxioms
import Quillen.Waldhausen.Approximation.SplitDeloopingEquivalence
import Quillen.Waldhausen.Approximation.JointEndpoints
import Quillen.Waldhausen.Approximation.RelativeSplitMono
import Quillen.Waldhausen.Approximation.QuotientWeakEquivalences

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless (`Quillen.Waldhausen.Approximation).isPrefixOf origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  logInfo m!"Audited all {count} approximation-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.splitComparison_approximation
#print axioms Quillen.Waldhausen.splitSubcategoryFunctorialFactorization
#print axioms Quillen.Waldhausen.FunctorialFactorization.flagInclusionClassifyingHomotopyEquiv
#print axioms Quillen.Waldhausen.quotientNatTrans_weak
#print axioms Quillen.Waldhausen.rowInitialFlagClassifyingHomotopyEquiv
#print axioms Quillen.Waldhausen.splitRowInclusionClassifyingHomotopyEquiv
#print axioms Quillen.Waldhausen.weakRowDiagonalIso
#print axioms Quillen.Waldhausen.splitDeloopingHomotopyEquiv
#print axioms Quillen.Waldhausen.splitDeloopingHomotopyEquiv_toFun
