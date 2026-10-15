/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarChartPause
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareRectangleFaces

/-! Exact coefficient naturality rectangle in the common diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The one merged simplex for the three native geometric triples of this coefficient rectangle. -/
def simplex := DoubleSquareMergedSimplex.simplex
  (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
  (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
  (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P (α.app c))
  (coefficientTransformation_naturality P α u).symm
  (coefficientTransformation_naturality P α v).symm

/-- Every parameter of the native coefficient rectangle uses the common scalar surface. -/
theorem rectangle_nativeLift :
    HomotopyLift (simplex P α u v) DoubleSquareScalarPaths.rectangleParameter
      (CoefficientTransformationComposition.rectangle P α u v) :=
  DoubleSquareScalarPaths.original_rectangle_nativeLift
    (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
    (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm

/-- The actual `ofLevels` coefficient comparison retains the reversed scalar path coordinate. -/
theorem comparison_nativeLift :
    HomotopyLift (simplex P α u v) DoubleSquareScalarPaths.rectangleParameter.symm₂
      (CoefficientTransformationComposition.comparison P α u v) := by
  intro n r s x
  exact (HomotopyLift.symmPath _ (rectangle_nativeLift P α u v)) n r s x

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
