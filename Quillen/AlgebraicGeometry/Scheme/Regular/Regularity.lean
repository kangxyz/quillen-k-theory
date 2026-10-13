/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular schemes through their actual local rings

Regularity means local noetherianity and regularity of every structure-sheaf
stalk. The affine-chart criterion is proved using the actual open-immersion
stalk isomorphisms and the spectrum stalk/localization isomorphism.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.Scheme

/-- The usual local-ring definition of a regular scheme. -/
class IsRegular (X : AlgebraicGeometry.Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  regular_stalk (x : X) : IsRegularLocalRing (X.presheaf.stalk x)

attribute [instance] IsRegular.regular_stalk

/-- Regularity restricts along an actual open immersion. -/
theorem isRegular_of_isOpenImmersion {U X : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsRegular X] : IsRegular U where
  toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
  regular_stalk x := IsRegularLocalRing.of_ringEquiv
    (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv

/-- Every affine chart of a regular scheme has an actually regular ring. -/
theorem regular_affineChart {X : AlgebraicGeometry.Scheme.{u}} [IsRegular X]
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j] : IsRegularRing R := by
  have : IsNoetherianRing R := CoherentScheme.noetherian_affineChart R j
  have : IsRegular (Spec R) := isRegular_of_isOpenImmersion j
  apply isRegularRing_iff.mpr
  intro p hp
  have : IsRegularLocalRing ((Spec R).presheaf.stalk (⟨p, hp⟩ : PrimeSpectrum R)) :=
    IsRegular.regular_stalk _
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso R (⟨p, hp⟩ : PrimeSpectrum R)).commRingCatIsoToRingEquiv

/-- The spectrum of a regular ring is regular in the local-ring definition. -/
instance isRegular_spec (R : CommRingCat.{u}) [IsRegularRing R] : IsRegular (Spec R) where
  regular_stalk x := IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso R x).symm.commRingCatIsoToRingEquiv

/-- On an actual spectrum, scheme regularity is precisely ring regularity. -/
theorem isRegular_spec_iff (R : CommRingCat.{u}) : IsRegular (Spec R) ↔ IsRegularRing R := by
  constructor
  · intro h
    exact regular_affineChart R (𝟙 _)
  · intro h
    infer_instance

/-- Regularity on every actual affine open chart is equivalent to the
standard stalk definition. No finite-dimensionality condition is present. -/
theorem isRegular_iff_affineCharts (X : AlgebraicGeometry.Scheme.{u}) :
    IsRegular X ↔ ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      IsRegularRing R := by
  constructor
  · intro h R j _
    exact regular_affineChart R j
  · intro h
    have : IsLocallyNoetherian X :=
      (isLocallyNoetherian_iff_openCover X.affineOpenCover.openCover).mpr (by
        intro i
        have : IsOpenImmersion (X.affineOpenCover.f i) := X.affineOpenCover.map_prop i
        have := h (X.affineOpenCover.X i) (X.affineOpenCover.f i)
        exact isLocallyNoetherian_Spec.mpr inferInstance)
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := X.affineOpenCover.openCover.exists_eq x
    have : IsOpenImmersion (X.affineOpenCover.f i) := X.affineOpenCover.map_prop i
    have := h (X.affineOpenCover.X i) (X.affineOpenCover.f i)
    have := IsRegular.regular_stalk (X := Spec (X.affineOpenCover.X i)) y
    have H := IsRegularLocalRing.of_ringEquiv
      (asIso ((X.affineOpenCover.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv
    change (X.affineOpenCover.f i) y = x at hy
    subst x
    exact H

end Quillen.Scheme
