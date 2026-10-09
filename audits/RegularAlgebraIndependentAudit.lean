import Quillen.Scheme.Regular.AffineFiniteDimension
import Lean.Util.CollectAxioms

/-! Independent current-module-origin audit, including private/generated constants. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Algebra.RegularLocal.ParameterAvoidance,
    `Quillen.Algebra.RegularLocal.ParameterQuotient,
    `Quillen.Algebra.RegularLocal.Domain,
    `Quillen.Algebra.RegularLocal.Parameters,
    `Quillen.Algebra.RegularLocal.QuotientLifting,
    `Quillen.Algebra.RegularLocal.ProjectiveDimension,
    `Quillen.Scheme.Regular.GeneralComparison,
    `Quillen.Scheme.Regular.AffineFiniteDimension]
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
open CategoryTheory AlgebraicGeometry

example (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  Quillen.RegularLocal.isDomain_of_regularLocal R

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d + 1 : ℕ)) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular R x ∧
      IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) = (d : ℕ) :=
  Quillen.RegularLocal.exists_regular_parameter R d hd

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ :=
  Quillen.RegularLocal.projectiveDimension_ne_top_of_regularLocal R M

example (R : CommRingCat.{u}) [IsRegularRing R] [FiniteRingKrullDim R] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (Spec R) n) :=
  Quillen.Scheme.KToG_regular_finiteDimension_bijective R n

example (R : CommRingCat.{u}) [IsRegularRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) (n : ℕ) :
    (Quillen.Scheme.KToGRegularFiniteDimensionEquiv R d hd n).toMonoidHom =
      Quillen.Scheme.KToG (Spec R) n := rfl

example (R : CommRingCat.{u}) [IsRegularRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) (n : ℕ)
    (x : Quillen.Scheme.K (Spec R) n) :
    Quillen.Scheme.KToGRegularFiniteDimensionEquiv R d hd n x =
      Quillen.Scheme.KToG (Spec R) n x := rfl

#check @Quillen.RegularLocal.hasProjectiveDimensionLE_of_regularLocal_dimension
#check @Quillen.RegularLocal.finiteProjectiveResolution_of_regularLocal
#check @Quillen.CoherentScheme.hasProjectiveDimensionLE_of_regular_dimension_le
#check @Quillen.SchemeSheaf.schemeKToG_bijective_of_finite_resolutions
#check @Quillen.Scheme.KToG_regular_finiteDimension_bijective
#print axioms Quillen.Scheme.KToG_regular_finiteDimension_bijective
#print axioms Quillen.Scheme.KToGRegularFiniteDimensionEquiv_toMonoidHom
