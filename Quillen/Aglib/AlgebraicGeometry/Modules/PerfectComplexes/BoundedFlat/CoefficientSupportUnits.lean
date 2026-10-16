/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportSections
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismNaturality

/-!
# Actual units on the original localization-support sections

The specified coefficient unit and forward Laurent automorphism retain the same original supported section maps and coefficient preservation.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The original joint section unit restricted through the actual supported inclusion. -/
def boundedFlatCoefficientSupportedUnitIso (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    𝟭 (BoundedFlatCoefficientSupportSections f a) ≅ 𝟭 (BoundedFlatCoefficientSupportSections f a) :=
  lift (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedFlatCoefficientSectionUnitIso (op Q, a) (boundedFlatCoefficientUnit (op Q, a) r))

/-- Forgetting support keeps precisely the original forward unit component. -/
theorem boundedFlatCoefficientSupportedUnitIso_hom
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) (S : BoundedFlatCoefficientSupportSections f a) :
    ((boundedFlatCoefficientSupportedUnitIso f a r).hom.app S).hom =
      (boundedFlatCoefficientSectionUnitIso (op Q, a)
        (boundedFlatCoefficientUnit (op Q, a) r)).hom.app S.obj :=
  map_lift_hom (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι _ S

/-- The actual forward Laurent coordinate on the original supported coefficient fiber. -/
def boundedFlatCoefficientSupportedLaurentUnitIso (a : Under R) :=
  boundedFlatCoefficientSupportedUnitIso f ((laurentUnderFunctor R).obj a)
    (laurentGlobalUnit a.right)

/-- Actual supported coefficient reindexing preserves the same native forward Laurent unit. -/
theorem boundedFlatCoefficientSupportedLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedFlatCoefficientSupportedModelFunctor f).map
      ((laurentUnderFunctor R).map g)).functor
      (boundedFlatCoefficientSupportedLaurentUnitIso f a)
      (boundedFlatCoefficientSupportedLaurentUnitIso f b) := by
  change Preserves (boundedFlatCoefficientSupportedSectionsMap
    (schemeMap f ((laurentUnderFunctor R).obj a)) (schemeMap f ((laurentUnderFunctor R).obj b))
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientOpenPairMap f ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientOpenPairMap f ((laurentUnderFunctor R).map g)).hom)) _ _
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)).map
      ((boundedFlatCoefficientSupportedLaurentUnitIso f a).hom.app S).hom = _
  dsimp only [boundedFlatCoefficientSupportedLaurentUnitIso]
  rw [boundedFlatCoefficientSupportedUnitIso_hom, boundedFlatCoefficientSupportedUnitIso_hom]
  simpa only [boundedFlatCoefficientSectionLaurentUnitIso,
    boundedFlatCoefficientSupportedSectionsMap, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj] using
      boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g S.obj

end Quillen.PerfectComplexes

end

end
