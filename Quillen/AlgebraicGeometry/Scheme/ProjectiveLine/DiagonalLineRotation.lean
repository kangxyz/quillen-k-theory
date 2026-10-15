/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.SingleShift
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationNaturality

/-!
# Exact line tensor and rotation of the diagonal generation triangle

Apply the exact tensor by the original tautological line and rotate the natural
vector-bundle triangle, retaining the negative shifted incidence. The literal
single-complex chain-map vanishing does not assert derived-morphism vanishing.
No nested line contraction, corrected roof representative, or extension to arbitrary
coefficient complexes is encoded here.

The base ring is arbitrary, including the zero ring. These interfaces preserve
the accepted vector-bundle scope; they do not establish a projective-bundle
equivalence or a full coefficient extension.
-/

@[expose] public section
open Quillen


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.DiagonalRoofObstruction
export CochainComplex
  (chainMap_single_zero_to_shift_one_eq_zero)
end Quillen.DiagonalRoofObstruction

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DerivedCategory
  CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
local instance lineRotationStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- Apply the actual exact tensor with L and rotate once, retaining the standard
negative sign on the shifted incidence morphism. -/
def diagonalLineRotatedTriangle (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    Triangle (DerivedCategory.Plus (twoChartLine R).Modules) :=
  ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
    R)).rightDerivedFunctorPlus.mapTriangle.obj
    (diagonalGenerationTriangle R E)).rotate

/-- Tensor by the actual finite locally free line and rotation preserve distinguishedness. -/
theorem diagonalLineRotatedTriangle_distinguished (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    diagonalLineRotatedTriangle R E ∈ distTriang (DerivedCategory.Plus (twoChartLine R).Modules) :=
  rot_of_distTriang _
    ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
      R)).rightDerivedFunctorPlus.map_distinguished _
      (diagonalGenerationTriangle_distinguished R E))

/-- The third rotated vertex is canonically L tensor p*(Rp*(E tensor L)[1]),
using the installed shift comparison of the original composite exact functor. -/
def diagonalLineRotatedThirdIso (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    (diagonalLineRotatedTriangle R E).obj₃ ≅
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine R)).rightDerivedFunctorPlus.obj
        ((derivedFlatPullbackPlus (projection R)).obj
          (((derivedPushforwardPlus (projection R)).obj
            ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj
              ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalLine R))))⟦(1 :
                ℤ)⟧)) :=
  ((derivedFlatPullbackPlus (projection R) ⋙
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
      R)).rightDerivedFunctorPlus).commShiftIso
      (1 : ℤ)).symm.app _

/-- The actual line-tensored and rotated maps form triangle morphisms. -/
def diagonalLineRotatedTriangleMap
    {E E' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] (f : E ⟶ E') :
    diagonalLineRotatedTriangle R E ⟶ diagonalLineRotatedTriangle R E' :=
  (CategoryTheory.Pretriangulated.rotate _).map
    ((moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
      R)).rightDerivedFunctorPlus.mapTriangle.map
      (diagonalGenerationTriangleMap R f))

/-- Identity coefficient arrows are retained after the actual exact tensor and rotation. -/
theorem diagonalLineRotatedTriangleMap_id (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] :
    diagonalLineRotatedTriangleMap R (𝟙 E) = 𝟙 (diagonalLineRotatedTriangle R E) := by
  dsimp only [diagonalLineRotatedTriangleMap]
  rw [diagonalGenerationTriangleMap_id,
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
      R)).rightDerivedFunctorPlus.mapTriangle.map_id,
    (CategoryTheory.Pretriangulated.rotate _).map_id]
  rfl

/-- Composition of coefficient arrows is retained after tensor and rotation. -/
theorem diagonalLineRotatedTriangleMap_comp
    {E E' E'' : (twoChartLine R).Modules} [IsFiniteLocallyFree (twoChartLine R) E]
    [IsFiniteLocallyFree (twoChartLine R) E'] [IsFiniteLocallyFree (twoChartLine R) E'']
    (f : E ⟶ E') (g : E' ⟶ E'') :
    diagonalLineRotatedTriangleMap R (f ≫ g) =
      diagonalLineRotatedTriangleMap R f ≫ diagonalLineRotatedTriangleMap R g := by
  dsimp only [diagonalLineRotatedTriangleMap]
  rw [diagonalGenerationTriangleMap_comp,
    (moduleTensorLeftFunctor (twoChartLine R) (tautologicalLine
      R)).rightDerivedFunctorPlus.mapTriangle.map_comp,
    (CategoryTheory.Pretriangulated.rotate _).map_comp]

end AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.DiagonalRoofObstruction
variable {C : Type u} [Category.{v} C] [Abelian C]
end Quillen.DiagonalRoofObstruction
