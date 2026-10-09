import Lean.Util.CollectAxioms
import Quillen.Waldhausen.SplitComplexes.ExactSequences
import Quillen.Waldhausen.SplitComplexes.Factorization
import Quillen.PerfectComplexes.SplitSupport

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless (`Quillen.Waldhausen.SplitComplexes).isPrefixOf origin ||
      origin == `Quillen.PerfectComplexes.SplitKTheory ||
      origin == `Quillen.PerfectComplexes.SplitSupport do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  logInfo m!"Audited all {count} split-complex-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.splitComplexes
#print axioms Quillen.Waldhausen.splitComplexSubcategory
#print axioms Quillen.Waldhausen.splitSubcategoryCofibrations_iff
#print axioms Quillen.Waldhausen.SplitFactorization.exists_factorization
#print axioms Quillen.PerfectComplexes.SplitPerfectK
#print axioms Quillen.PerfectComplexes.splitPerfectToPerfectKMap
#print axioms Quillen.PerfectComplexes.splitPerfectKRestrict
#print axioms Quillen.PerfectComplexes.splitStrictSupportedToPerfectKMap
