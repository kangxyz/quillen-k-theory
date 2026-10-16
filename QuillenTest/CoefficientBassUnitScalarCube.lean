/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitScalarCube

/-! The scalar unit cube preserves the original entire chart face and the unpaused terminal
projection, including independence from the terminal comparison coordinate. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Convexity
open scoped Topology unitInterval
universe u
namespace QuillenTest.CoefficientBassUnitScalarCube
open Quillen.PerfectComplexes.CoefficientBassUnitScalarCube
open Quillen.PerfectComplexes.CoefficientBassUnitScalarEdges
open Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder

theorem entire_original_inverse_face (r s : unitInterval) :
    scalarCube.{u} ![r, s, 1] = StdSimplex.map minusSideIndex
      (Quillen.PerfectComplexes.OriginalUnitSquareSimplex.squareParameter (r, s)) :=
  cube_right r s

theorem terminal_projection_independent (s s' t : unitInterval) :
    scalarCube.{u} ![1, s, t] = scalarCube.{u} ![1, s', t] :=
  (cube_one s t).trans (cube_one s' t).symm

theorem terminal_positive_vertex (s : unitInterval) :
    scalarCube.{u} ![1, s, 0] = (StdSimplex.single 44 : StdSimplex ℝ (Fin 48)) := by
  rw [cube_one]
  change StdSimplex.map topIndex
    (Quillen.PerfectComplexes.CoefficientPolynomialSpanUnitTop.middleEnd 0) = _
  rw [Path.source, StdSimplex.map_single]
  rfl

end QuillenTest.CoefficientBassUnitScalarCube
