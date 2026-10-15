/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalTensorPushforward
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion

/-!
# Original diagonal-supported tensor identification for arbitrary coefficients

The actual closed-immersion projection formula removes the vector-bundle
coefficient assumption from the original diagonal-supported tensor comparison.
The forward map retains the original projection arrow and section-pullback map.
The existing vector-bundle isomorphism is recovered exactly.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

local instance allCoefficientDiagonalClosed (R : CommRingCat.{u}) :
    IsClosedImmersion (relativeDiagonal R) := isClosedImmersion_relativeDiagonal R

/-- The original diagonal-supported tensor identification for arbitrary module sheaves. -/
def diagonalTensorPushforwardIsoAll (R : CommRingCat.{u})
    (E M : (twoChartLine R).Modules) :
    (moduleTensorLeftFunctor (relativeSquare R)
      ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).obj M) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).obj
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj M) :=
  closedImmersionProjectionFormulaIso (relativeDiagonal R)
      ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E) M ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).mapIso
      ((moduleTensorRightFunctor (twoChartLine R) M).mapIso
        ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
          (relativeDiagonal_first R)).app E))

/-- The forward arrow keeps the original projection unit and diagonal section identification. -/
theorem diagonalTensorPushforwardIso_all_hom (R : CommRingCat.{u})
    (E M : (twoChartLine R).Modules) :
    (diagonalTensorPushforwardIsoAll R E M).hom =
      projectionFormulaMap (relativeDiagonal R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E) M ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).map
        ((moduleTensorCoefficientMap (twoChartLine R)
          ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
            (relativeDiagonal_first R)).hom.app E)).app M) := rfl

/-- On vector-bundle coefficients this is exactly the existing original isomorphism. -/
theorem diagonalTensorPushforwardIso_all_eq (R : CommRingCat.{u})
    (E : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) E]
    (M : (twoChartLine R).Modules) :
    diagonalTensorPushforwardIsoAll R E M = diagonalTensorPushforwardIso R E M := by
  apply Iso.ext
  rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
