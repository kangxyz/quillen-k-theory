/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportRestriction
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare

/-!
# Actual coefficient units on supported native sections

The same forward unit is lifted through the original supported inclusions. Its coefficient equations and restriction preservation retain the stated original maps.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The actual coefficient unit restricted through the original supported section inclusion. -/
def boundedFlatCoefficientSupportSectionUnitIso {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ) :
    𝟭 (BoundedFlatCoefficientSupportedSections j) ≅
      𝟭 (BoundedFlatCoefficientSupportedSections j) :=
  lift (boundedFlatCoefficientSectionSupported j).ι
    (boundedFlatCoefficientSectionUnitIso i (boundedFlatCoefficientUnit i r))

/-- Forgetting support retains exactly the original forward coefficient-unit component. -/
theorem boundedFlatCoefficientSupportSectionUnitIso_hom {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] (r : (Γ(Spec i.2.right, ⊤))ˣ)
    (S : BoundedFlatCoefficientSupportedSections j) :
    ((boundedFlatCoefficientSupportSectionUnitIso j r).hom.app S).hom =
      (boundedFlatCoefficientSectionUnitIso i (boundedFlatCoefficientUnit i r)).hom.app S.obj :=
  map_lift_hom (boundedFlatCoefficientSectionSupported j).ι _ S

theorem supportMap_preserves_lift {i k : Index R} {U V : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (η : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      η)
    (α : 𝟭 (BoundedFlatCoefficientSections i) ≅ 𝟭 (BoundedFlatCoefficientSections i))
    (β : 𝟭 (BoundedFlatCoefficientSections k) ≅ 𝟭 (BoundedFlatCoefficientSections k))
    (hαβ : Preserves (boundedFlatCoefficientSectionsMap η) α β) :
    Preserves (boundedFlatCoefficientSupportedSectionsMap j j' η l h)
      (lift (boundedFlatCoefficientSectionSupported j).ι α)
      (lift (boundedFlatCoefficientSectionSupported j').ι β) := by
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap η).map
    ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom
  rw [show ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    α.hom.app S.obj from map_lift_hom (boundedFlatCoefficientSectionSupported j).ι α S,
    show ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom =
      β.hom.app ((boundedFlatCoefficientSectionsMap η).obj S.obj) from
      map_lift_hom (boundedFlatCoefficientSectionSupported j').ι β _]
  exact hαβ S.obj

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original ambient Laurent unit on its actual auxiliary-supported native fiber. -/
def boundedFlatCoefficientSupportedAmbientLaurentUnitIso (Q : Over (Spec R))
    (T : Q.left.Opens) (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso Q a)

/-- The original restricted Laurent unit on the true open-side auxiliary support. -/
def boundedFlatCoefficientSupportedFullOpenLaurentUnitIso (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso P a)

omit [IsOpenImmersion f.left] in
/-- Actual ambient supported coefficient reindexing preserves the original Laurent coordinate. -/
theorem boundedFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient
    (Q : Over (Spec R)) (T : Q.left.Opens) {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedFlatCoefficientSupportedAmbientMap T ((laurentUnderFunctor R).map g))
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T b) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientSupportPairMap Q T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

omit [IsOpenImmersion f.left] in
/-- Actual open-side supported coefficient reindexing preserves the same Laurent coordinate. -/
theorem boundedFlatCoefficientSupportedFullOpenLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves (boundedFlatCoefficientSupportedOpenMap f T ((laurentUnderFunctor R).map g))
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a)
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T b) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op P), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientOpenSupportPairMap f T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient P g)

omit [IsOpenImmersion f.left] in
/-- The actual supported restriction preserves each forward Laurent-unit component. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves (a : Under R) :
    Preserves (boundedFlatCoefficientSupportedOpenRestriction f T
      ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) :=
  supportMap_preserves_lift
    (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientOpenSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (f.op, 𝟙 ((laurentUnderFunctor R).obj a))
    (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportOpen Q T ((laurentUnderFunctor R).obj a))).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_restriction f a)

omit [IsOpenImmersion f.left] in
/-- Supported restriction retains every original coefficient scalar through its actual map. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_coefficientUnit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSupportedOpenRestriction f T a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r)
      (boundedFlatCoefficientSupportSectionUnitIso
        (boundedFlatCoefficientOpenSupportOpen f T a).ι r) :=
  supportMap_preserves_lift (boundedFlatCoefficientSupportOpen Q T a).ι
    (boundedFlatCoefficientOpenSupportOpen f T a).ι (f.op, 𝟙 a)
    (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).hom.left
    (Arrow.w (supportRestrictionPair (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).hom)
    _ _ (boundedFlatCoefficientSectionsRestriction_unit_preserves f a r)

end Quillen.PerfectComplexes

end

end
