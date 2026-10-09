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


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

example {A : Type u} [Category.{v} A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    ∃ (M : CochainComplex A ℤ) (i : K ⟶ M) (p : M ⟶ L),
      Quillen.Waldhausen.degreewiseSplitMono i ∧ QuasiIso p ∧ i ≫ p = f :=
  Quillen.Waldhausen.SplitFactorization.exists_factorization f

example (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    Quillen.PerfectComplexes.SplitPerfectK X n →* Quillen.PerfectComplexes.PerfectK X n :=
  Quillen.PerfectComplexes.splitPerfectToPerfectKMap X n

example {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Quillen.PerfectComplexes.SplitPerfectK X n →* Quillen.PerfectComplexes.SplitPerfectK U n :=
  Quillen.PerfectComplexes.splitPerfectKRestrict j n
