/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineRestrictionCoefficients
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.Algebra.Polynomial.LaurentModuleCech
public import Quillen.LinearAlgebra.Prod

/-! # Actual chart modules and their signed restriction maps

The positive and negative scalar structures are respectively T and T inverse.
Quasicoherence supplies the original overlap comparison; no chart freeness is assumed.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.PolynomialLaurent
namespace Quillen.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The polynomial module of sections on the original positive chart. -/
def plusChartModule : ModuleCat.{u} (Polynomial R) :=
  moduleSpecΓFunctor.obj (M.restrict (plusChart R))

/-- The polynomial module of sections on the original negative chart. -/
def minusChartModule : ModuleCat.{u} (Polynomial R) :=
  moduleSpecΓFunctor.obj (M.restrict (minusChart R))

/-- The actual negative and positive iterated restrictions identified on the common overlap. -/
def overlapRestrictionIso :
    (M.restrict (minusChart R)).restrict (laurentMinus R) ≅
      (M.restrict (plusChart R)).restrict (laurentPlus R) :=
  (Scheme.Modules.restrictFunctorComp (laurentMinus R) (minusChart R)).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorCongr (overlap_equation R).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (laurentPlus R) (plusChart R)).app M

/-- The original overlap transition with distinct negative and positive scalar structures. -/
def chartModuleOverlapIso [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (Quillen.LaurentProjector.negativeScalarMap R)).obj
        (minusChartModule R M) ≅
      (ModuleCat.extendScalars (Polynomial.toLaurent (R := R))).obj (plusChartModule R M) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Quillen.LaurentProjector.negativeScalarMap R))) :=
    inferInstanceAs (IsOpenImmersion (laurentMinus R))
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) :=
    inferInstanceAs (IsOpenImmersion (laurentPlus R))
  exact affineRestrictGlobalSectionsIso (CommRingCat.ofHom
      (Quillen.LaurentProjector.negativeScalarMap R)) (M.restrict (minusChart R)) ≪≫
    moduleSpecΓFunctor.mapIso (overlapRestrictionIso R M) ≪≫
    (affineRestrictGlobalSectionsIso (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (M.restrict (plusChart R))).symm

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

/-- The positive scalar map is the original open chart overlap. -/
local instance plusOpen : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) :=
  inferInstanceAs (IsOpenImmersion (laurentPlus R))

/-- The negative scalar map is the original open chart overlap. -/
local instance minusOpen : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (negativeScalarMap R))) :=
  inferInstanceAs (IsOpenImmersion (laurentMinus R))

/-- The signed difference of the original two affine restriction maps. -/
def chartSectionDifference :
    ((restrictScalars (Polynomial.C : R →+* Polynomial R)).obj (plusChartModule R M) ×
      (restrictScalars (Polynomial.C : R →+* Polynomial R)).obj (minusChartModule R M)) →ₗ[R]
        (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).obj
          (moduleSpecΓFunctor.obj ((M.restrict (plusChart R)).restrict (laurentPlus R))) :=
  (coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
      (M.restrict (plusChart R))).hom.comp (LinearMap.fst R _ _) -
    ((coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (negativeScalarMap R))
        (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
        (M.restrict (minusChart R)) ≫
      (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
        (moduleSpecΓFunctor.map (overlapRestrictionIso R M).hom)).hom).comp
          (LinearMap.snd R _ _)

/-- Positive scalar extension identified with the original overlap sections. -/
def chartOverlapSectionsIso [M.IsQuasicoherent] :=
  (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).mapIso
    (affineRestrictGlobalSectionsIso (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (M.restrict (plusChart R)))

/-- The overlap transition preserves both original restriction comparisons. -/
theorem chartModuleOverlapIso_hom_positive [M.IsQuasicoherent] :
    (chartModuleOverlapIso R M).hom ≫
      (affineRestrictGlobalSectionsIso (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
        (M.restrict (plusChart R))).hom =
    (affineRestrictGlobalSectionsIso (CommRingCat.ofHom (negativeScalarMap R))
        (M.restrict (minusChart R))).hom ≫
      moduleSpecΓFunctor.map (overlapRestrictionIso R M).hom := by
  simp [chartModuleOverlapIso]

/-- The positive scalar-extension unit is the original positive restriction map. -/
theorem plusSectionRestriction_coordinates [M.IsQuasicoherent] :
    restrictedExtensionUnit Polynomial.C (Polynomial.toLaurent (R := R)) LaurentPolynomial.C
        (positive_constants R) (plusChartModule R M) ≫ (chartOverlapSectionsIso R M).hom =
      coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
        (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
        (M.restrict (plusChart R)) := by
  simpa only [chartOverlapSectionsIso, Functor.mapIso_hom, plusChartModule,
    CommRingCat.hom_ofHom] using (coefficientRestrictionMap_eq
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
      (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))
      (CommRingCat.ofHom LaurentPolynomial.C) (positive_constants R)
      (M.restrict (plusChart R))).symm

/-- The negative scalar-extension unit retains the original negative restriction and transition. -/
theorem minusSectionRestriction_coordinates [M.IsQuasicoherent] :
    (restrictedExtensionUnit Polynomial.C (negativeScalarMap R) LaurentPolynomial.C
        (negative_constants R) (minusChartModule R M) ≫
      (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
        (chartModuleOverlapIso R M).hom) ≫ (chartOverlapSectionsIso R M).hom =
    coefficientRestrictionMap (CommRingCat.ofHom Polynomial.C)
        (CommRingCat.ofHom (negativeScalarMap R))
        (CommRingCat.ofHom LaurentPolynomial.C) (negative_constants R)
        (M.restrict (minusChart R)) ≫
      (restrictScalars (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map
        (moduleSpecΓFunctor.map (overlapRestrictionIso R M).hom) := by
  change (_ ≫ _) ≫ (restrictScalars
    (LaurentPolynomial.C : R →+* LaurentPolynomial R)).map _ = _
  rw [Category.assoc, ← Functor.map_comp, chartModuleOverlapIso_hom_positive,
    Functor.map_comp, ← Category.assoc]
  congr 1
  simpa only [minusChartModule, CommRingCat.hom_ofHom] using
    (coefficientRestrictionMap_eq (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
      (CommRingCat.ofHom (negativeScalarMap R)) (CommRingCat.ofHom LaurentPolynomial.C)
      (negative_constants R) (M.restrict (minusChart R))).symm

/-- The algebraic signed differential becomes the original chart restriction difference. -/
theorem chartSectionDifference_coordinates [M.IsQuasicoherent] :
    (chartOverlapSectionsIso R M).hom.hom.comp
      (moduleDifference (R := R) (plusChartModule R M) (minusChartModule R M)
        (chartModuleOverlapIso R M)) = chartSectionDifference R M := by
  apply LinearMap.postcompose_pairDifference
  · exact congrArg ModuleCat.Hom.hom (plusSectionRestriction_coordinates R M)
  · exact congrArg ModuleCat.Hom.hom (minusSectionRestriction_coordinates R M)

end Quillen.Scheme.ProjectiveLine
end

end
