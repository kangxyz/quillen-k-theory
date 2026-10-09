import Quillen.Scheme.Regular.GlobalComparison
import Lean.Util.CollectAxioms

/-! Independent all-origin audit of the frozen eight-module global endpoint. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Scheme.VectorBundle.Locality,
    `Quillen.Scheme.Regular.KernelClosure,
    `Quillen.Scheme.Regular.Regularity,
    `Quillen.Scheme.Regular.ResolutionProperty,
    `Quillen.Scheme.Regular.AffineChartDimension,
    `Quillen.Scheme.Regular.ChartBounds,
    `Quillen.Scheme.Regular.GlobalResolution,
    `Quillen.Scheme.Regular.GlobalComparison]
  let mut total : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless modules.contains origin do continue
    total := total + 1
    counts := counts.insert origin ((counts.find? origin).getD 0 + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for origin in modules do
    let count := (counts.find? origin).getD 0
    unless count > 0 do throwError "No declarations from required origin {origin}"
    logInfo m!"MODULE {origin}: {count} declarations"
  logInfo m!"Audited all {total} declarations in {modules.size} exact source modules, including private/generated declarations; only propext, Classical.choice, Quot.sound."

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

example (X : AlgebraicGeometry.Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG X n) :=
  Quillen.Scheme.KToG_regular_resolutionProperty_bijective X n

example (X : AlgebraicGeometry.Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ) :
    (Quillen.Scheme.KToGRegularEquiv X n).toMonoidHom = Quillen.Scheme.KToG X n := rfl

example (X : AlgebraicGeometry.Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ)
    (x : Quillen.Scheme.K X n) :
    Quillen.Scheme.KToGRegularEquiv X n x = Quillen.Scheme.KToG X n x := rfl

example (X : AlgebraicGeometry.Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X]
    (M : Quillen.CoherentScheme.Coherent X) :
    Nonempty ((Quillen.CoherentScheme.coherentExactStructure X).FiniteResolution
      (Quillen.SchemeSheaf.coherentVectorBundle X) M) :=
  Quillen.SchemeSheaf.coherentResolutionHypothesis_of_regular_resolutionProperty M

example (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]
    (h : ∀ M : Quillen.CoherentScheme.Coherent X,
      ∃ V : Quillen.SchemeSheaf.FiniteLocallyFree X,
        ∃ p : V.obj ⟶ M.obj, Epi p) :
    Quillen.Scheme.HasResolutionProperty X :=
  (Quillen.Scheme.hasResolutionProperty_iff_sheaf_epi X).mpr h

example (X : AlgebraicGeometry.Scheme.{u})
    (h : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j], IsRegularRing R) :
    Quillen.Scheme.IsRegular X := (Quillen.Scheme.isRegular_iff_affineCharts X).mpr h

example (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]
    [Quillen.Scheme.HasResolutionProperty X] (U : X.AffineOpenCover.{v})
    (n : ℕ) (M : Quillen.CoherentScheme.Coherent X)
    (h : Quillen.SchemeSheaf.AffineCoverDimensionLE U M n) :
    ∃ T : (Quillen.CoherentScheme.coherentExactStructure X).FiniteResolution
      (Quillen.SchemeSheaf.coherentVectorBundle X) M, T.length ≤ n :=
  Quillen.SchemeSheaf.coherentResolution_length_le_of_affineCoverDimensionLE U n M h

example (R : CommRingCat.{u}) [IsNoetherianRing R] :
    Quillen.Scheme.HasResolutionProperty (Spec R) := inferInstance

example (R : CommRingCat.{u}) : Quillen.Scheme.IsRegular (Spec R) ↔ IsRegularRing R :=
  Quillen.Scheme.isRegular_spec_iff R

example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    Quillen.Scheme.KToGRegularEquiv (Spec R) n =
      Quillen.Scheme.KToGRegularAffineEquiv R n :=
  Quillen.Scheme.KToGRegularEquiv_spec R n

#check @Quillen.Scheme.KToG_regular_resolutionProperty_bijective
#check @Quillen.Scheme.KToGRegularEquiv_restrict
#print axioms Quillen.Scheme.KToG_regular_resolutionProperty_bijective
#print axioms Quillen.Scheme.KToGRegularEquiv_spec
