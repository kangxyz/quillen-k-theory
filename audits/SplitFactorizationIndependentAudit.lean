import Lean.Util.CollectAxioms
import Quillen.Waldhausen.SplitComplexes.ExactSequences
import Quillen.Waldhausen.SplitComplexes.Factorization
import Quillen.PerfectComplexes.SplitSupport
import Quillen.PerfectComplexes.SplitFactorization

open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[`Quillen.Waldhausen.SplitComplexes.Basic,
    `Quillen.Waldhausen.SplitComplexes.Subcategory,
    `Quillen.Waldhausen.SplitComplexes.ExactSequences,
    `Quillen.Waldhausen.SplitComplexes.Factorization,
    `Quillen.Waldhausen.SplitComplexes.FactorizationQuotient,
    `Quillen.Waldhausen.SplitComplexes.FactorizationSubcategory,
    `Quillen.PerfectComplexes.SplitKTheory,
    `Quillen.PerfectComplexes.SplitSupport,
    `Quillen.PerfectComplexes.SplitFactorization]
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
      throwError "Required source module has no audited declarations: {origin}"
  logInfo m!"Audited all {count} split-complex-origin declarations, including private/generated declarations; only propext, Classical.choice, Quot.sound."

#print axioms Quillen.Waldhausen.splitComplexes
#print axioms Quillen.Waldhausen.splitComplexSubcategory
#print axioms Quillen.Waldhausen.splitSubcategoryCofibrations_iff
#print axioms Quillen.Waldhausen.SplitFactorization.exists_factorization
#print axioms Quillen.PerfectComplexes.SplitPerfectK
#print axioms Quillen.PerfectComplexes.splitPerfectToPerfectKMap
#print axioms Quillen.PerfectComplexes.splitPerfectKRestrict
#print axioms Quillen.PerfectComplexes.splitStrictSupportedToPerfectKMap

#print axioms Quillen.Waldhausen.SplitFactorization.quotientSequenceSplitting
#print axioms Quillen.Waldhausen.SplitFactorization.quotientSequence_shortExact
#print axioms Quillen.Waldhausen.SplitFactorization.exists_subcategory_factorization
#print axioms Quillen.PerfectComplexes.locallyPerfect_mappingCone
#print axioms Quillen.PerfectComplexes.exists_splitStrict_factorization
#print axioms Quillen.PerfectComplexes.exists_splitPerfect_factorization

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

example {X : AlgebraicGeometry.Scheme.{u}}
    {K L : Quillen.PerfectComplexes.Perfect X} (f : K ⟶ L) :
    ∃ (M : Quillen.PerfectComplexes.Perfect X) (i : K ⟶ M) (p : M ⟶ L),
      (Quillen.PerfectComplexes.splitPerfectWaldhausen X).cof i ∧
      (Quillen.PerfectComplexes.splitPerfectWaldhausen X).weq p ∧ i ≫ p = f :=
  Quillen.PerfectComplexes.exists_splitPerfect_factorization f

example {X : AlgebraicGeometry.Scheme.{u}}
    {K L : Quillen.PerfectComplexes.StrictPerfect X} (f : K ⟶ L) :
    ∃ (M : Quillen.PerfectComplexes.StrictPerfect X) (i : K ⟶ M) (p : M ⟶ L),
      (Quillen.PerfectComplexes.splitStrictWaldhausen X).cof i ∧
      (Quillen.PerfectComplexes.splitStrictWaldhausen X).weq p ∧ i ≫ p = f :=
  Quillen.PerfectComplexes.exists_splitStrict_factorization f
