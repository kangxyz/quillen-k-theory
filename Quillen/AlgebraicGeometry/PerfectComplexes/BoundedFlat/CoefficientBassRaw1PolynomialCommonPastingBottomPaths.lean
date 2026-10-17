/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingPaths

/-!
# Original bottom paths of the actual common-sheet pasting

All ten original paths retain their complete Laurent18 parameters at height zero.
The four radial paths and six cap paths use the fixed common polynomial reference,
the existing complete source-chart transports, and their unchanged binary clocks.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottomPaths
open CommonReferenceNerve
open CoefficientBassRaw1PolynomialTripleRoutes
open CoefficientBassRaw1PolynomialCommonPastingPaths
open CoefficientBassRaw1PolynomialTripleLowerFaces
open CoefficientBassRaw1PolynomialCapLowerFaces
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

private theorem first_left_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.firstFace BassH0Merge.leftIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.sourceChart r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (BassH0Merge.leftIndex i))
    0 1 2 r

private theorem first_right_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.firstFace BassH0Merge.rightIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.firstRestriction r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.firstFace.toOrderHom (BassH0Merge.rightIndex i))
    0 1 2 r

private theorem middle_right_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.middleFace BassH0Merge.rightIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.secondRestriction r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (BassH0Merge.rightIndex i))
    0 1 2 r

private theorem middle_left_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.middleFace BassH0Merge.leftIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.middleChart r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.middleFace.toOrderHom (BassH0Merge.leftIndex i))
    0 1 2 r

private theorem last_left_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.lastFace BassH0Merge.leftIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.lastRestriction r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (BassH0Merge.leftIndex i))
    0 1 2 r

private theorem last_right_row
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialCapLowerFaces.row P α β f
      DoubleSquareMergedSimplex.lastFace BassH0Merge.rightIndex r =
    parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.targetChart r) := by
  apply congrArg (parameter (targetReference P α β f) (nodes P α β f))
  exact BassSupportOrder.map_any_binary
    (fun i ↦ DoubleSquareMergedSimplex.lastFace.toOrderHom (BassH0Merge.rightIndex i))
    0 1 2 r

variable (negative : Bool)
local notation "β" => chartChoice negative

/-- The complete radial A bottom is the original sourceTotal path. -/
theorem radialA_bottom (r : I) :
    radialA P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.sourceTotal r)) :=
  CoefficientBassRaw1PolynomialCommonRadialCaps.first_left_lower P α β f r

/-- The complete radial B bottom is the original firstIntermediate path. -/
theorem radialB_bottom (r : I) :
    radialB P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.firstIntermediate r)) :=
  CoefficientBassRaw1PolynomialCommonRadialCaps.first_right_lower P α β f r

/-- The complete radial C bottom is the original middleTotal path. -/
theorem radialC_bottom (r : I) :
    radialC P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.middleTotal r)) :=
  CoefficientBassRaw1PolynomialCommonRadialCaps.middle_left_lower P α β f r

/-- The complete radial D bottom is the original targetTotal path. -/
theorem radialD_bottom (r : I) :
    radialD P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.targetTotal r)) :=
  CoefficientBassRaw1PolynomialCommonRadialCaps.last_right_lower P α β f r

/-- The complete cap X bottom is the original sourceChart path. -/
theorem capX_bottom (r : I) :
    capX P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.sourceChart r)) := by
  cases negative
  · exact (first_plus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurent R) f)
        (first_left_row P α f (underToLaurent R) r))
  · exact (first_minus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurentInvert R) f)
        (first_left_row P α f (underToLaurentInvert R) r))

/-- The complete cap Y bottom is the original firstRestriction path. -/
theorem capY_bottom (r : I) :
    capY P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.firstRestriction r)) := by
  exact (first_input_lower P α β f r).trans
    (congrArg (laurent P α β f) (first_right_row P α f β r))

/-- The complete cap Z bottom is the original secondRestriction path. -/
theorem capZ_bottom (r : I) :
    capZ P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.secondRestriction r)) := by
  exact (middle_input_lower P α β f r).trans
    (congrArg (laurent P α β f) (middle_right_row P α f β r))

/-- The complete cap W bottom is the original middleChart path. -/
theorem capW_bottom (r : I) :
    capW P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.middleChart r)) := by
  cases negative
  · exact (middle_plus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurent R) f)
        (middle_left_row P α f (underToLaurent R) r))
  · exact (middle_minus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurentInvert R) f)
        (middle_left_row P α f (underToLaurentInvert R) r))

/-- The complete cap V bottom is the original lastRestriction path. -/
theorem capV_bottom (r : I) :
    capV P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.lastRestriction r)) := by
  cases negative
  · exact (last_plus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurent R) f)
        (last_left_row P α f (underToLaurent R) r))
  · exact (last_minus_postcomp_lower P α f r).trans
      (congrArg (laurent P α (underToLaurentInvert R) f)
        (last_left_row P α f (underToLaurentInvert R) r))

/-- The complete cap U bottom is the original targetChart path. -/
theorem capU_bottom (r : I) :
    capU P α f negative r 0 =
    laurent P α β f (parameter (targetReference P α β f) (nodes P α β f)
      (DoubleSquareScalarPaths.targetChart r)) := by
  exact (last_input_lower P α β f r).trans
    (congrArg (laurent P α β f) (last_right_row P α f β r))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingBottomPaths
