/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientCoordinate
public import QuillenTest.LineCoordinateChart
public import QuillenTest.LineCoordinateUnit
public import Mathlib.Data.ZMod.Basic

/-! Original coordinate, scalar and support consumers for arbitrary perfect coefficients. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.PolynomialLaurent
namespace QuillenTest.TautologicalCoefficientCoordinate

/-- The coordinate is tensor of the literal original first-coordinate arrow. -/
theorem original_first_coordinate (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientPerfectCoordinate R K).hom =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit
        (tautologicalFirstCoordinate R)).app K.obj := rfl

/-- Cancelling the actual negative chart comparison yields the original coefficient scalar. -/
theorem original_negative_coordinate_scalar (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tensorByLineComplexChartIso (minusChart R) (tautologicalLine R)
        (tautologicalLineMinusIso R)).inv.app K.obj ≫
      (restrict (minusChart R)).map (tautologicalCoefficientPerfectCoordinate R K).hom =
        (complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
          ((restrict (minusChart R)).obj K.obj) := by
  change _ ≫ (restrict (minusChart R)).map
    ((tautologicalCoefficientCoordinate R).app K.obj) = _
  rw [tautologicalCoefficientCoordinate_minus]
  simp

/-- The support object is the literal signed cone of the exact original coefficient arrow. -/
theorem original_supported_cone (R : CommRingCat.{u})
    (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientSupportedCone R K).obj =
      CochainComplex.mappingCone
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit
          (tautologicalFirstCoordinate R)).app K.obj) := rfl

/-- The positive original coordinate remains invertible over the zero ring. -/
theorem zero_ring_positive_coordinate_isIso
    (K : Perfect (twoChartLine (.of (ZMod 1)))) :
    IsIso ((restrict (plusChart (.of (ZMod 1)))).map
      (tautologicalCoefficientPerfectCoordinate (.of (ZMod 1)) K).hom) :=
  tautologicalCoefficientCoordinate_plus_isIso _ _

end QuillenTest.TautologicalCoefficientCoordinate
