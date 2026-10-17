/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrected

/-! Whole endpoint words of the prescribed corrected polynomial cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
open CommonReferenceNerve CoefficientBassRaw1PolynomialPairEndpointRows
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original correction fixes its entire initial height path. -/
theorem corrected_zero (s : I) : corrected P β p q (0, s) =
    lowerPath P β p q s := (correctedSquare P β p q).at_zero s

/-- The original correction retains the specified right-associated terminal word. -/
theorem corrected_one (s : I) : corrected P β p q (1, s) =
    ((firstPath P β p q).trans
      ((secondPath P β p q).trans (thirdPath P β p q))) s :=
  (correctedSquare P β p q).at_one s

/-- The direct original chart boundary keeps all five full reference nodes. -/
theorem chartSquare_zero (s : I) : chartSquare P β p q (0, s) =
    laurent P β p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
        (rowNodes P β p q 0) (NativeSquareFiveSimplex.parameter s)) :=
  congrArg (laurent P β p q) (sheetFamily_zero P β p q s)

/-- The first terminal path is the whole first chart row, with its literal half clock. -/
theorem firstPath_row (s : I) : firstPath P β p q s =
    laurent P β p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
        (rowNodes P β p q 1) (NativeSquareFiveSimplex.parameter s)) := by
  change chartSquare P β p q (1, Quillen.NativePathCells.lower s) = _
  exact congrArg (laurent P β p q) (sheetFamily_one_lower P β p q s)

/-- The second terminal path is the whole second chart row at its independent half clock. -/
theorem secondPath_row (s : I) : secondPath P β p q s =
    laurent P β p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
        (rowNodes P β p q 2) (NativeSquareFiveSimplex.parameter s)) := by
  change chartSquare P β p q (1, Quillen.NativePathCells.upper s) = _
  exact congrArg (laurent P β p q) (sheetFamily_one_upper P β p q s)

/-- The final path keeps the original paused polynomial input and unchanged cone height. -/
theorem thirdPath_cylinder (s : I) : thirdPath P β p q s =
    cylinder P β p q
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, s) := rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
