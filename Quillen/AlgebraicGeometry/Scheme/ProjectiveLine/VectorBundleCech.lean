/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechSections
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineProjective
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Restriction
public import Quillen.Algebra.ModuleComplex.LaurentModuleCech

/-! # Finite-projective Cech models for actual vector bundles

For an arbitrary commutative base ring, a finite locally free sheaf on the
original two-chart line has a finite-projective two-term model for its actual
signed Cech differential. The result includes an actual chain homotopy equivalence;
it makes no assertion about arbitrary perfect complexes or derived generation.
-/

@[expose] public section
open Quillen


section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)
/-- A finite locally free sheaf has a finite module of positive-chart sections. -/
theorem plusChartModule_finite [IsFiniteLocallyFree (twoChartLine R) M] :
    Module.Finite (Polynomial R) (plusChartModule R M) :=
  finite_globalSections_of_finiteLocallyFree (.of (Polynomial R)) (M.restrict (plusChart R))

/-- A finite locally free sheaf has a finite module of negative-chart sections. -/
theorem minusChartModule_finite [IsFiniteLocallyFree (twoChartLine R) M] :
    Module.Finite (Polynomial R) (minusChartModule R M) :=
  finite_globalSections_of_finiteLocallyFree (.of (Polynomial R)) (M.restrict (minusChart R))

/-- A finite locally free sheaf has a projective module of positive-chart sections. -/
theorem plusChartModule_projective [IsFiniteLocallyFree (twoChartLine R) M] :
    Module.Projective (Polynomial R) (plusChartModule R M) :=
  projective_globalSections_of_finiteLocallyFree (.of (Polynomial R)) (M.restrict (plusChart R))

/-- A finite locally free sheaf has a projective module of negative-chart sections. -/
theorem minusChartModule_projective [IsFiniteLocallyFree (twoChartLine R) M] :
    Module.Projective (Polynomial R) (minusChartModule R M) :=
  projective_globalSections_of_finiteLocallyFree (.of (Polynomial R)) (M.restrict (minusChart R))

end AlgebraicGeometry.Scheme.ProjectiveLine
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules Quillen.LaurentProjector Quillen.ModuleComplex
namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The algebraic Laurent Cech complex identified with the original chart-section complex. -/
def chartSectionCechIso [M.IsQuasicoherent] :
    linearMapCechComplex (moduleDifference (R := R) (plusChartModule R M)
      (minusChartModule R M) (chartModuleOverlapIso R M)) ≅
    linearMapCechComplex (chartSectionDifference R M) :=
  linearMapCechIsoOfEquivs _ _ (LinearEquiv.refl _ _)
    (chartOverlapSectionsIso R M).toLinearEquiv (by
      simpa using chartSectionDifference_coordinates R M)

/-- The original chart-section differential has a finite-projective model in degrees zero and
one.
-/
theorem exists_chartSectionDifference_model [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (chartSectionDifference R M)) P) := by
  have := plusChartModule_finite R M
  have := minusChartModule_finite R M
  have := plusChartModule_projective R M
  have := minusChartModule_projective R M
  obtain ⟨P, hP, hfin, ⟨h⟩⟩ := exists_moduleDifference_model_of_finite_projective
    (plusChartModule R M) (minusChartModule R M) (chartModuleOverlapIso R M)
  exact ⟨P, hP, hfin, ⟨(HomotopyEquiv.ofIso (chartSectionCechIso R M).symm).trans h⟩⟩

end AlgebraicGeometry.Scheme.ProjectiveLine
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
  Quillen.ModuleComplex
namespace AlgebraicGeometry.Scheme.ProjectiveLine
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The original sheaf-difference complex identified with its actual chart coordinates. -/
def originalCechCoordinateIso :
    linearMapCechComplex
      (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
        (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
          (plusChart R) (minusChart R) (overlap_equation R) M))).hom ≅
      linearMapCechComplex (chartSectionDifference R M) :=
  linearMapCechIsoOfEquivs _ _ (originalCechSourceIso R M).toLinearEquiv
    (overlapLocalizedSectionsIso R M).toLinearEquiv
    (congrArg ModuleCat.Hom.hom (original_sheafDifference_sections R M))

/-- A finite locally free sheaf has an actual finite-projective model of its original signed
Cech complex.
-/
theorem exists_original_vectorBundle_cech_model [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv
        (linearMapCechComplex
          (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (projection R)).map
            (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
              (plusChart R) (minusChart R) (overlap_equation R) M))).hom) P) := by
  obtain ⟨P, hP, hfin, ⟨h⟩⟩ := exists_chartSectionDifference_model R M
  exact ⟨P, hP, hfin, ⟨(HomotopyEquiv.ofIso (originalCechCoordinateIso R M)).trans h⟩⟩

end AlgebraicGeometry.Scheme.ProjectiveLine
end

end
