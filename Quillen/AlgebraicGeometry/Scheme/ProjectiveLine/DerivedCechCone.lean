/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedCechTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechSheafComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # The original derived projective-line Cech cone

The actual derived two-chart triangle identifies the original derived direct image of a
quasicoherent sheaf with its original signed sheaf Cech cone. Both ordinary vertices are
fixed by identity maps, the original connecting square is retained, and the minus-one
shift is explicit. No coefficient perfection is assumed. -/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
namespace AlgebraicGeometry.Scheme.ProjectiveLine
/-- The standard ambient derived category of original module sheaves. -/
local instance derivedCechConeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) [M.IsQuasicoherent]

/-- Compare the rotated original derived triangle with the literal signed cone triangle. -/
def derivedCechConeTriangleIso :
    ((DerivedCategory.Plus.ι.mapTriangle).obj (derivedCechTriangle R M)).rotate ≅
      DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle
          ((single (Spec R).Modules (.up ℤ) 0).map
            ((Scheme.Modules.pushforward (projection R)).map
              (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
                (plusChart R) (minusChart R) (overlap_equation R) M)))) := by
  refine isoTriangleOfIso₁₂ _ _
    (rot_of_distTriang _ (DerivedCategory.Plus.ι.map_distinguished _
      (derivedCechTriangle_distinguished R M)))
    (DerivedCategory.mappingCone_triangle_distinguished _) (Iso.refl _) (Iso.refl _) ?_
  change DerivedCategory.Q.map
      ((single (Spec R).Modules (.up ℤ) 0).map
        ((Scheme.Modules.pushforward (projection R)).map
          (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
            (plusChart R) (minusChart R) (overlap_equation R) M))) ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- The original source term of the signed difference is unchanged. -/
theorem derivedCechConeTriangleIso_hom_hom₁ :
    (derivedCechConeTriangleIso R M).hom.hom₁ = 𝟙 _ := by
  simp [derivedCechConeTriangleIso]

/-- The original overlap term of the signed difference is unchanged. -/
theorem derivedCechConeTriangleIso_hom_hom₂ :
    (derivedCechConeTriangleIso R M).hom.hom₂ = 𝟙 _ := by
  simp [derivedCechConeTriangleIso]

/-- The comparison retains the actual connecting arrow of the original derived triangle. -/
theorem derivedCechConeTriangleIso_connecting :
    ((DerivedCategory.Plus.ι.mapTriangle).obj (derivedCechTriangle R M)).mor₃ ≫
        (derivedCechConeTriangleIso R M).hom.hom₃ =
      (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle
          ((single (Spec R).Modules (.up ℤ) 0).map
            ((Scheme.Modules.pushforward (projection R)).map
              (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
                (plusChart R) (minusChart R) (overlap_equation R) M))))).mor₂ := by
  have e := (derivedCechConeTriangleIso R M).hom.comm₂
  simpa [derivedCechConeTriangleIso] using e

/-- The original derived direct image is the original signed sheaf cone shifted by minus one. -/
def derivedCechConeIso :
    DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
      DerivedCategory.Q.obj (originalSheafCechComplex R M) :=
  ((shiftFunctorCompIsoId (DerivedCategory (Spec R).Modules) (1 : ℤ) (-1) (by omega)).app _).symm ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (Spec R).Modules) (-1 : ℤ)).mapIso
      (Triangle.π₃.mapIso (derivedCechConeTriangleIso R M)) ≪≫
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app _).symm

end AlgebraicGeometry.Scheme.ProjectiveLine
