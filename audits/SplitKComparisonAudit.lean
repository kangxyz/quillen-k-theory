import Lean.Util.CollectAxioms
import Quillen.PerfectComplexes.SplitComparison
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
    unless (`Quillen.Waldhausen.Approximation).isPrefixOf origin ||
      origin == `Quillen.PerfectComplexes.SplitComparison do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  logInfo m!"Audited all {count} approximation/comparison-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.splitComplexSubcategoryKMap_bijective
#print axioms Quillen.Waldhausen.splitComplexSubcategoryKEquiv
#print axioms Quillen.PerfectComplexes.splitStrictToStrictKMap_bijective
#print axioms Quillen.PerfectComplexes.splitPerfectToPerfectKMap_bijective
#print axioms Quillen.PerfectComplexes.splitStrictKEquiv
#print axioms Quillen.PerfectComplexes.splitPerfectKEquiv

universe u

open AlgebraicGeometry in
example (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (Quillen.PerfectComplexes.splitPerfectToPerfectKMap X n) :=
  Quillen.PerfectComplexes.splitPerfectToPerfectKMap_bijective X n
