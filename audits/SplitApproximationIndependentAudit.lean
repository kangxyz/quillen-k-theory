import Lean.Util.CollectAxioms
import Quillen.PerfectComplexes.SplitFactorization
import Quillen.Waldhausen.Approximation.SplitDeloopingEquivalence
import Quillen.Waldhausen.Approximation.JointEndpoints
import Quillen.Waldhausen.Approximation.RelativeSplitMono
import Quillen.Waldhausen.Approximation.QuotientWeakEquivalences

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Waldhausen.Approximation.FactorizationData,
    `Quillen.Waldhausen.Approximation.FiniteReplacement,
    `Quillen.Waldhausen.Approximation.FlagRowEquivalence,
    `Quillen.Waldhausen.Approximation.FunctorialFactorization,
    `Quillen.Waldhausen.Approximation.JointEndpoints,
    `Quillen.Waldhausen.Approximation.Properties,
    `Quillen.Waldhausen.Approximation.QuotientWeakEquivalences,
    `Quillen.Waldhausen.Approximation.RelativeSplitMono,
    `Quillen.Waldhausen.Approximation.SequenceReplacement,
    `Quillen.Waldhausen.Approximation.SplitDeloopingEquivalence,
    `Quillen.Waldhausen.Approximation.SplitRowEquivalence,
    `Quillen.Waldhausen.Approximation.WeakFlags,
    `Quillen.Waldhausen.Approximation.WeakRowDiagonal,
    `Quillen.Waldhausen.Approximation.WeakRowSimplicial,
    `Quillen.Waldhausen.Approximation.WeakRows]
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    counts := counts.insert origin ((counts.find? origin).getD 0 + 1)
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for origin in modules do
    if (counts.find? origin).getD 0 == 0 then
      throwError "Missing required source origin {origin}"
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

noncomputable section
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
open Quillen.Waldhausen Quillen.PerfectComplexes

example (X : Scheme.{u}) : ContinuousMap.HomotopyEquiv
    (splitStrictWaldhausen X).Delooping (strictWaldhausen X).Delooping :=
  splitDeloopingHomotopyEquiv (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)

example (X : Scheme.{u}) : ContinuousMap.HomotopyEquiv
    (splitPerfectWaldhausen X).Delooping (perfectWaldhausen X).Delooping :=
  splitDeloopingHomotopyEquiv (locallyPerfect X)
    (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f)

example (X : Scheme.{u}) :
    (splitDeloopingHomotopyEquiv (locallyPerfect X)
      (fun hK hL f ↦ locallyPerfect_mappingCone hK hL f)).toFun =
    (deloopingMap (splitComplexSubcategory_to_complexSubcategory_exact
      (locallyPerfect X))).hom :=
  splitDeloopingHomotopyEquiv_toFun _ _
