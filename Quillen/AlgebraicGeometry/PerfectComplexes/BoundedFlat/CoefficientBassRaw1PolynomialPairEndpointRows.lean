/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerAttachment

/-! Complete original five-node endpoint rows of the paused polynomial cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairEndpointRows
open CommonReferenceNerve CoefficientMovingSquareRows

/-- The original terminal pause leaves the entire direct source boundary unchanged. -/
theorem paused_zero_row (s : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s) =
    StdSimplex.map outerRow (NativeSquareFiveSimplex.parameter s) := by
  change collapsed (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter)
    (0, s) = _
  rw [collapsed_zero_path]
  exact (BassSupportOrder.map_two_binary outerRow 0 1 2 3 4 s).symm

/-- The first original terminal half is unchanged by the right-edge pause. -/
theorem paused_one_lower_row (s : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s) =
    StdSimplex.map firstRow (NativeSquareFiveSimplex.parameter s) := by
  change collapsed (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter)
    (1, lower s) = _
  rw [collapsed_top_path]
  exact (moving_one (lower s)).symm.trans (moving_one_lower_row s)

/-- The second original terminal half retains its separate native chart clock. -/
theorem paused_one_upper_row (s : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s) =
    StdSimplex.map secondRow (NativeSquareFiveSimplex.parameter s) := by
  change collapsed (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter)
    (1, upper s) = _
  rw [collapsed_top_path]
  exact (moving_one (upper s)).symm.trans (moving_one_upper_row s)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Full endpoint nodes keep the original sheet anchor and all native square references. -/
def rowNodes (j : Fin 3) (i : Fin 5) :
    Node (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q) :=
  CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)
    (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q
      (![outerRow, firstRow, secondRow] j i))

private theorem row_parameter (j : Fin 3) (s : I) :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
      (parameter (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
        (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q)
        (StdSimplex.map (![outerRow, firstRow, secondRow] j)
          (NativeSquareFiveSimplex.parameter s))) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
      (rowNodes P β p q j) (NativeSquareFiveSimplex.parameter s) := by
  rw [mapParameter_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  rw [← hz]
  exact parameter_supported _ _ _ (![outerRow, firstRow, secondRow] j)
    (fun _ ↦ rfl) (BassH1Support.edgeFace i) (primitive_rows_monotone j i) z

/-- The whole zero endpoint row retains its original clock and reference. -/
theorem sheetFamily_zero (s : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (0, s) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
      (rowNodes P β p q 0) (NativeSquareFiveSimplex.parameter s) := by
  change mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s))) = _
  rw [paused_zero_row]
  exact row_parameter P β p q 0 s

/-- The whole one lower endpoint row retains its original clock and reference. -/
theorem sheetFamily_one_lower (s : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (1, lower s) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
      (rowNodes P β p q 1) (NativeSquareFiveSimplex.parameter s) := by
  change mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s))) = _
  rw [paused_one_lower_row]
  exact row_parameter P β p q 1 s

/-- The whole one upper endpoint row retains its original clock and reference. -/
theorem sheetFamily_one_upper (s : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (1, upper s) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
      (rowNodes P β p q 2) (NativeSquareFiveSimplex.parameter s) := by
  change mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s))) = _
  rw [paused_one_upper_row]
  exact row_parameter P β p q 2 s

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairEndpointRows
