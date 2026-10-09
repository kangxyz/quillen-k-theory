import Quillen.Scheme.Regular.Affine
import Lean.Util.CollectAxioms

/-! Independent compactness/globalization and canonical-forward-map audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Algebra.RegularLocal.GlobalProjectiveDimension,
    `Quillen.Scheme.Regular.Affine]
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
attribute [local instance] Abelian.hasFiniteBiproducts

example (R : Type u) [CommRing R] [IsRegularRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] : projectiveDimension M ≠ ⊤ :=
  Quillen.CoherentScheme.projectiveDimension_ne_top_of_regular R M

example (R : Type u) [CommRing R] [IsRegularRing R] :
    (Quillen.CoherentScheme.finiteModuleExactStructure.{u, u} R).ResolutionHypothesis
      (Quillen.CoherentScheme.finiteProjective R) :=
  Quillen.CoherentScheme.finiteProjectiveResolutionHypothesis_of_regular R

example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (Spec R) n) :=
  Quillen.Scheme.KToG_regular_affine_bijective R n

example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    (Quillen.Scheme.KToGRegularAffineEquiv R n).toMonoidHom =
      Quillen.Scheme.KToG (Spec R) n := rfl

example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ)
    (x : Quillen.Scheme.K (Spec R) n) :
    Quillen.Scheme.KToGRegularAffineEquiv R n x =
      Quillen.Scheme.KToG (Spec R) n x := rfl

example {R S : CommRingCat.{u}} [IsRegularRing R] [IsRegularRing S]
    (j : Spec S ⟶ Spec R) [IsOpenImmersion j] (n : ℕ)
    (x : Quillen.Scheme.K (Spec R) n) :
    Quillen.Scheme.restrictG j n (Quillen.Scheme.KToGRegularAffineEquiv R n x) =
      Quillen.Scheme.KToGRegularAffineEquiv S n (Quillen.Scheme.restrictK j n x) :=
  Quillen.Scheme.KToGRegularAffineEquiv_restrict j n x

#check @Quillen.CoherentScheme.projectiveDimension_ne_top_of_localized
#check @Quillen.CoherentScheme.projectiveDimension_ne_top_of_regular
#check @Quillen.CoherentScheme.finiteProjectiveResolutionHypothesis_of_regular
#check @Quillen.SchemeSheaf.coherentResolutionHypothesis_of_regular
#check @Quillen.Scheme.KToG_regular_affine_bijective
#check @Quillen.Scheme.KToGRegularAffineEquiv
#check @Quillen.Scheme.KToGRegularAffineEquiv_restrict
#print axioms Quillen.Scheme.KToG_regular_affine_bijective
#print axioms Quillen.Scheme.KToGRegularAffineEquiv_toMonoidHom
#print axioms Quillen.Scheme.KToGRegularAffineEquiv_restrict
