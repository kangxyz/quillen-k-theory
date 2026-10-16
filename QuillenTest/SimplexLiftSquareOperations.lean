/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftSquareOperations
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSimplex

/-! Extract the complete three-sided boundary of the actual original geometric unit square
through the new scalar operation; both times and the native degree-zero level are retained. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open Quillen.PerfectComplexes.OriginalUnitSquareSimplex
open scoped Topology unitInterval
universe u
namespace QuillenTest.SimplexLiftSquareOperations

theorem original_unit_boundary {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HomotopyLift (simplex f) (ParameterSquare.ofBoundary rotatedParameter).toBoundary
      (boundedFlatPerfectPrespectrumUnitSquare f).toBoundary :=
  SquareLift.toBoundary (simplex f) (square_native f)

/-- Reversal followed by boundary extraction retains the original midpoint, with independent
comparison time and native input at every level. -/
theorem original_unit_reversed_boundary_midpoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex f) n
      ((ParameterSquare.ofBoundary rotatedParameter).reversePaths.toBoundary
        (r, ⟨1 / 2, by constructor <;> norm_num⟩), x) =
      (boundedFlatPerfectPrespectrumUnitSquare f).reversePaths.toBoundary.level n
        (r, (⟨1 / 2, by constructor <;> norm_num⟩, x)) :=
  (SquareLift.toBoundary (simplex f)
    (SquareLift.reversePaths (simplex f)
      (Q := ParameterSquare.ofBoundary rotatedParameter)
      (N := boundedFlatPerfectPrespectrumUnitSquare f) (square_native f))) n r _ x

end QuillenTest.SimplexLiftSquareOperations
