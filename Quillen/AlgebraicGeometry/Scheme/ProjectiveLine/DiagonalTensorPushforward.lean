/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.ProjectionFormula
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalIncidence
/-!
# Tensor with a sheaf supported on the original relative diagonal

Apply the ordinary projection formula to the actual relative diagonal and use
its original section-pullback identification with the first projection. The
coefficient is any finite locally free sheaf on the genuine two-chart line;
the sheaf pushed along the diagonal is arbitrary. The forward arrow retains
the original geometric unit and the original section-pullback map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The original diagonal-supported tensor identification for a vector bundle. -/
def diagonalTensorPushforwardIso (R : CommRingCat.{u}) (E : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) E] (M : (twoChartLine R).Modules) :
    (moduleTensorLeftFunctor (relativeSquare R)
      ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).obj M) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).obj
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj M) :=
  projectionFormulaIso (relativeDiagonal R)
      ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E) M ≪≫
    (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).mapIso
      ((moduleTensorRightFunctor (twoChartLine R) M).mapIso
        ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
          (relativeDiagonal_first R)).app E))
/-- The forward map uses the literal projection arrow and original diagonal section map. -/
theorem diagonalTensorPushforwardIso_hom (R : CommRingCat.{u})
    (E : (twoChartLine R).Modules) [IsFiniteLocallyFree (twoChartLine R) E]
    (M : (twoChartLine R).Modules) :
    (diagonalTensorPushforwardIso R E M).hom =
      projectionFormulaMap (relativeDiagonal R)
        ((AlgebraicGeometry.Scheme.Modules.pullback (relativeFirst R)).obj E) M ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeDiagonal R)).map
        ((moduleTensorCoefficientMap (twoChartLine R)
          ((sectionPullbackIso (relativeDiagonal R) (relativeFirst R)
            (relativeDiagonal_first R)).hom.app E)).app M) := rfl
end Quillen.Scheme.ProjectiveLine
