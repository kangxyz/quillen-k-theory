import Quillen.Scheme.Regular.GlobalComparison
import Lean.Util.CollectAxioms

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
    let source := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]!
      | none => Name.anonymous
    if modules.contains source then
      total := total + 1
      counts := counts.insert source ((counts.find? source).getD 0 + 1)
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
      logInfo m!"CHECKED {name}: {dependencies}"
  for source in modules do
    let count := (counts.find? source).getD 0
    if count == 0 then throwError "No declarations audited in required source module {source}"
    logInfo m!"MODULE {source}: {count} declarations"
  logInfo m!"PASS: {total} declarations in {modules.size} exact source modules; only propext, Classical.choice, Quot.sound."

universe u
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
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X]
    (M : Quillen.CoherentScheme.Coherent X) :
    Nonempty ((Quillen.CoherentScheme.coherentExactStructure X).FiniteResolution
      (Quillen.SchemeSheaf.coherentVectorBundle X) M) :=
  Quillen.SchemeSheaf.coherentResolutionHypothesis_of_regular_resolutionProperty M

example (R : CommRingCat.{u}) [IsNoetherianRing R] :
    Quillen.Scheme.HasResolutionProperty (Spec R) := inferInstance

example (R : CommRingCat.{u}) : Quillen.Scheme.IsRegular (Spec R) ↔ IsRegularRing R :=
  Quillen.Scheme.isRegular_spec_iff R

example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    Quillen.Scheme.KToGRegularEquiv (Spec R) n =
      Quillen.Scheme.KToGRegularAffineEquiv R n :=
  Quillen.Scheme.KToGRegularEquiv_spec R n

#check @Quillen.Scheme.hasResolutionProperty_iff_sheaf_epi
#check @Quillen.Scheme.isRegular_iff_affineCharts
#check @Quillen.SchemeSheaf.coherentResolution_length_le_of_affineCoverDimensionLE
#check @Quillen.Scheme.KToGRegularEquiv_restrict
#print axioms Quillen.Scheme.KToG_regular_resolutionProperty_bijective
#print axioms Quillen.Scheme.KToGRegularEquiv_spec
