/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientGeometry
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedCoefficientGeometry

/-!
# The original auxiliary support pairs and their integral row comparison

The support inclusion over the integer base is base changed using the original coefficient
construction. Its actual open range is the old auxiliary support open. The resulting pair
isomorphism retains the ambient identity and then the original canonical row symmetry.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient

variable {R : CommRingCat.{u}} (Q : Over (Spec R)) (T : Q.left.Opens)

/-- The actual support open with its original structure map to the coefficient base. -/
def supportObject : Over (Spec R) := Over.mk (T.ι ≫ Q.hom)

/-- The original support inclusion as a morphism over the base. -/
def supportArrow : supportObject Q T ⟶ Q := Over.homMk T.ι rfl

/-- The original support inclusion is still the given open immersion over the base. -/
instance supportArrow_isOpenImmersion : IsOpenImmersion (supportArrow Q T).left :=
  inferInstanceAs (IsOpenImmersion T.ι)

/-- Base change of the actual support inclusion has precisely the old support open. -/
theorem supportArrow_range (a : Under R) :
    (schemeMap (supportArrow Q T) a).opensRange =
      boundedFlatCoefficientSupportOpen Q T a := by
  rw [Scheme.Hom.opensRange_of_isPullback (schemeMap (supportArrow Q T) a)
    (projection (op (supportObject Q T), a)) (projection (op Q, a))
    (supportArrow Q T).left (schemeMap_isPullback (supportArrow Q T) a)]
  change projection (op Q, a) ⁻¹ᵁ T.ι.opensRange = _
  rw [Scheme.Opens.opensRange_ι]
  rfl

/-- The old support-open scheme is the actual open range of the base-changed inclusion. -/
def supportRangeIso (a : Under R) :
    ((boundedFlatCoefficientSupportOpen Q T a) : Scheme.{u}) ≅ space (op (supportObject Q T), a) :=
  IsOpenImmersion.isoOfRangeEq (boundedFlatCoefficientSupportOpen Q T a).ι
    (schemeMap (supportArrow Q T) a) (by
      change ((boundedFlatCoefficientSupportOpen Q T a).ι.opensRange : Set (space (op Q, a))) =
        ((schemeMap (supportArrow Q T) a).opensRange : Set (space (op Q, a)))
      rw [Scheme.Opens.opensRange_ι, supportArrow_range])

/-- The range identification retains the original support inclusion itself. -/
theorem supportRangeIso_fac (a : Under R) :
    (supportRangeIso Q T a).hom ≫ schemeMap (supportArrow Q T) a =
      (boundedFlatCoefficientSupportOpen Q T a).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The old support pair and base-changed original support arrow are genuinely isomorphic. -/
def supportPairIso (a : Under R) :
    supportOpenPair (boundedFlatCoefficientSupportOpen Q T a) ≅
      boundedFlatCoefficientOpenPair (supportArrow Q T) a :=
  Scheme.openPairProperty.isoMk
    (Arrow.isoMk (supportRangeIso Q T a) (Iso.refl _) (by
      change (supportRangeIso Q T a).hom ≫ schemeMap (supportArrow Q T) a =
        (boundedFlatCoefficientSupportOpen Q T a).ι ≫ 𝟙 _
      rw [Category.comp_id]
      exact supportRangeIso_fac Q T a))

/-- The ambient corner of this pair comparison is literally the identity. -/
theorem supportPairIso_hom_right (a : Under R) :
    (supportPairIso Q T a).hom.hom.right = 𝟙 _ := rfl

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- The old native auxiliary support pair maps to the unchanged parameter support pair. -/
def parameterSupportPairIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    supportOpenPair (boundedFlatCoefficientSupportOpen Q T a) ≅
      GlobalSupportedParameter.pair T.ι (Spec a.right) :=
  supportPairIso Q T a ≪≫ GlobalSupportedParameter.coefficientPairIso (supportArrow Q T) a

/-- The whole pair comparison uses exactly the prescribed ambient row symmetry. -/
theorem parameterSupportPairIso_hom_right
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterSupportPairIso Q T a).hom.hom.right = (canonicalRowIso Q a).hom := by
  change 𝟙 _ ≫ (canonicalRowIso Q a).hom = _
  exact Category.id_comp _

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
