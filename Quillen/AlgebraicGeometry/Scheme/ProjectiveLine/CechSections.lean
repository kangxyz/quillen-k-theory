/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ModuleChartSections
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineChartSections
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSheafSequence
public import Quillen.Algebra.Category.ModuleCat.CartesianProduct
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # The original sheaf Cech difference in affine chart coordinates

The source and overlap comparisons preserve the literal TwoOpen.sheafDifference.
Both signs and the negative-chart overlap identification are retained.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent Quillen.LaurentProjector
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The positive overlap used by the original sheaf sequence is open. -/
local instance originalPlusOpen : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) :=
  inferInstanceAs (IsOpenImmersion (laurentPlus R))
/-- The negative overlap used by the original sheaf sequence is open. -/
local instance originalMinusOpen : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (negativeScalarMap R))) :=
  inferInstanceAs (IsOpenImmersion (laurentMinus R))

/-- Sections of the original positive localization, in affine coefficients. -/
def plusLocalizedSectionsIso :=
  (chartPushforwardSectionsIso (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    (plusChart R) (projection R) (plusChart_projection R)).app (M.restrict (plusChart R))

/-- Sections of the original negative localization, in affine coefficients. -/
def minusLocalizedSectionsIso :=
  (chartPushforwardSectionsIso (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    (minusChart R) (projection R) (minusChart_projection R)).app (M.restrict (minusChart R))

/-- Sections of the original positive overlap localization, in affine coefficients. -/
def overlapLocalizedSectionsIso :=
  (chartPushforwardSectionsIso (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (laurentPlus R ≫ plusChart R) (projection R)
    (nestedProjection (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
      (plusChart R) (projection R) (plusChart_projection R))).app
      (M.restrict (laurentPlus R ≫ plusChart R)) ≪≫
    (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).mapIso
      (moduleSpecΓFunctor.mapIso
        ((Scheme.Modules.restrictFunctorComp (laurentPlus R) (plusChart R)).app M))

/-- The actual sheaf product sections identified with the pair of chart modules. -/
def originalCechSourceIso :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (projection R)).obj
      ((openLocalization (plusChart R)).obj M ⨯ (openLocalization (minusChart R)).obj M)) ≅
    ModuleCat.of R
      ((restrictScalars (Polynomial.C : R →+* Polynomial R)).obj (plusChartModule R M) ×
        (restrictScalars (Polynomial.C : R →+* Polynomial R)).obj (minusChartModule R M)) := by
  letI : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
    (tilde.adjunction (R := R)).isRightAdjoint
  exact PreservesLimitPair.iso (Scheme.Modules.pushforward (projection R) ⋙ moduleSpecΓFunctor)
      ((openLocalization (plusChart R)).obj M) ((openLocalization (minusChart R)).obj M) ≪≫
    prod.mapIso (plusLocalizedSectionsIso R M) (minusLocalizedSectionsIso R M) ≪≫
    prodIsoCartesian _ _

/-- The first map of the original sheaf difference preserves affine restriction coordinates. -/
theorem original_plus_restriction :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (openLocalizationMap (laurentPlus R) (plusChart R) M)) ≫
      (overlapLocalizedSectionsIso R M).hom =
    (plusLocalizedSectionsIso R M).hom ≫
      coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
        (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
        (M.restrict (plusChart R)) := by
  exact original_nested_restriction (CommRingCat.ofHom Polynomial.C)
    (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
    (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
    (plusChart R) (projection R) (plusChart_projection R) M

end Quillen.Scheme.ProjectiveLine
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent Quillen.LaurentProjector
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The negative overlap remains the original open immersion. -/
local instance negativeCechMinusOpen : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (negativeScalarMap R))) :=
  inferInstanceAs (IsOpenImmersion (laurentMinus R))

/-- Sections of the negative overlap localization before the original overlap identification. -/
def negativeOverlapLocalizedSectionsIso :=
  (chartPushforwardSectionsIso (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (laurentMinus R ≫ minusChart R) (projection R)
    (nestedProjection (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (negativeScalarMap R))
      (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
      (minusChart R) (projection R) (minusChart_projection R))).app
      (M.restrict (laurentMinus R ≫ minusChart R)) ≪≫
    (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).mapIso
      (moduleSpecΓFunctor.mapIso
        ((Scheme.Modules.restrictFunctorComp (laurentMinus R) (minusChart R)).app M))

/-- The original equality of overlap arrows transports the actual section comparison. -/
theorem overlapLocalizedSectionsIso_congr :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        ((openLocalizationCongr (overlap_equation R).symm).hom.app M)) ≫
      (overlapLocalizedSectionsIso R M).hom =
    (negativeOverlapLocalizedSectionsIso R M).hom ≫
      (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
        (moduleSpecΓFunctor.map (overlapRestrictionIso R M).hom) := by
  have h := chartPushforwardSections_congr
    (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
    (projection R) (overlap_equation R).symm
    (nestedProjection (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (negativeScalarMap R))
      (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
      (minusChart R) (projection R) (minusChart_projection R))
    (nestedProjection (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
      (plusChart R) (projection R) (plusChart_projection R)) M
  have h' := congrArg (fun f => f ≫
    (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictFunctorComp (laurentPlus R) (plusChart R)).hom.app M))) h
  simpa only [CommRingCat.hom_ofHom, overlapLocalizedSectionsIso,
    negativeOverlapLocalizedSectionsIso,
    overlapRestrictionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc] using h'

/-- The negative nested localization retains the original coefficient restriction unit. -/
theorem original_negative_nested_restriction :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (openLocalizationMap (laurentMinus R) (minusChart R) M)) ≫
      (negativeOverlapLocalizedSectionsIso R M).hom =
    (minusLocalizedSectionsIso R M).hom ≫
      coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (negativeScalarMap R))
        (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
        (M.restrict (minusChart R)) := by
  exact original_nested_restriction (CommRingCat.ofHom Polynomial.C)
    (CommRingCat.ofHom (negativeScalarMap R))
    (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
    (minusChart R) (projection R) (minusChart_projection R) M

/-- The second map of the original sheaf difference preserves the negative restriction
coordinates.
-/
theorem original_minus_restriction :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (TwoOpen.sheafSecondRestriction (laurentPlus R) (laurentMinus R)
          (plusChart R) (minusChart R) (overlap_equation R) M)) ≫
      (overlapLocalizedSectionsIso R M).hom =
    (minusLocalizedSectionsIso R M).hom ≫
      coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (negativeScalarMap R))
        (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
        (M.restrict (minusChart R)) ≫
      (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
        (moduleSpecΓFunctor.map (overlapRestrictionIso R M).hom) := by
  simp only [TwoOpen.sheafSecondRestriction, Functor.map_comp, Category.assoc]
  rw [overlapLocalizedSectionsIso_congr, ← Category.assoc]
  rw [original_negative_nested_restriction, Category.assoc]

end Quillen.Scheme.ProjectiveLine
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent Quillen.LaurentProjector
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The original source comparison preserves the first categorical projection. -/
@[reassoc]
theorem originalCechSourceIso_hom_fst :
    (originalCechSourceIso R M).hom ≫ ofHom (LinearMap.fst R _ _) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (prod.fst : (openLocalization (plusChart R)).obj M ⨯
          (openLocalization (minusChart R)).obj M ⟶ _)) ≫
        (plusLocalizedSectionsIso R M).hom := by
  simp only [originalCechSourceIso, Iso.trans_hom, Category.assoc, prod.mapIso,
    PreservesLimitPair.iso_hom, Functor.comp_obj, CommRingCat.hom_ofHom,
    plusChartModule, minusChartModule]
  erw [prodIsoCartesian_hom_fst]
  erw [prod.map_fst, prodComparison_fst_assoc]
  rfl

/-- The original source comparison preserves the second categorical projection. -/
@[reassoc]
theorem originalCechSourceIso_hom_snd :
    (originalCechSourceIso R M).hom ≫ ofHom (LinearMap.snd R _ _) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (prod.snd : (openLocalization (plusChart R)).obj M ⨯
          (openLocalization (minusChart R)).obj M ⟶ _)) ≫
        (minusLocalizedSectionsIso R M).hom := by
  simp only [originalCechSourceIso, Iso.trans_hom, Category.assoc, prod.mapIso,
    PreservesLimitPair.iso_hom, Functor.comp_obj, CommRingCat.hom_ofHom,
    plusChartModule, minusChartModule]
  erw [prodIsoCartesian_hom_snd]
  erw [prod.map_snd, prodComparison_snd_assoc]
  rfl

end Quillen.Scheme.ProjectiveLine
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent Quillen.LaurentProjector
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The original TwoOpen sheaf difference becomes the literal signed chart-section map. -/
theorem original_sheafDifference_sections :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
          (plusChart R) (minusChart R) (overlap_equation R) M)) ≫
      (overlapLocalizedSectionsIso R M).hom =
    (originalCechSourceIso R M).hom ≫ ofHom (chartSectionDifference R M) := by
  let : (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
    (tilde.adjunction (R := R)).isRightAdjoint
  let : (moduleSpecΓFunctor (R := R)).Additive :=
    Functor.additive_of_preserves_binary_products _
  simp only [TwoOpen.sheafDifference, Functor.map_sub, Functor.map_comp,
    Preadditive.sub_comp, Category.assoc]
  erw [original_plus_restriction R M, original_minus_restriction R M]
  unfold chartSectionDifference
  erw [ModuleCat.ofHom_pairDifference]
  rw [Preadditive.comp_sub]
  erw [originalCechSourceIso_hom_fst_assoc R M,
    originalCechSourceIso_hom_snd_assoc R M]

end Quillen.Scheme.ProjectiveLine
end

end
