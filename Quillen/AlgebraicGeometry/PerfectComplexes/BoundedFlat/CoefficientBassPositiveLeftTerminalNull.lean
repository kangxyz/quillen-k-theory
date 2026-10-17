/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftTerminalParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace

/-! The unchanged terminal null words on both sheets.

The first old null is D.trans (H.trans (K.trans C17)), at first-route time zero.
Every whole piece is matched in the common carrier before using the accepted corrected
square's at_one boundary. No terminal seed equality or native cancellation is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalNull
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftConeSquares CoefficientBassPositiveLeftTerminalParameters
open CoefficientBassPositiveLeftPolynomialParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The two actual C1 starts, retaining their separate reference-bearing unit endpoints. -/
def terminalStart (e : Bool) : Carrier P p q :=
  if e then CoefficientBassPositiveC1SeedFace.shiftedStart P p q 1
  else CoefficientBassPositiveC1SeedFace.ordinaryStart P p q 1

/-- D uses the original source-positive binary path, with both full endpoint joins proved. -/
def D (e : Bool) : Path (terminalStart P p q e)
    (includeLaurent P p q (oldChartParameter P p q e 0)) where
  toFun s := includeLaurent P p q (oldPositiveParameter P p q e s)
  continuous_toFun := by fun_prop
  source' := by
    cases e
    · exact (congrArg (includeLaurent P p q) (positive_ordinary P p q 0)).trans
        ((CoefficientBassPositiveC1SeedFace.positiveMinus P p q).apply_zero 1)
    · exact (congrArg (includeLaurent P p q) (positive_shifted P p q 0)).trans
        ((CoefficientBassPositiveC1SeedFace.positivePlus P p q).apply_zero 1)
  target' := by
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.D BassH0Diagram.plusFace 1)) =
      includeLaurent P p q (parameter _ _
        (ProjectionRectangleParameters.L BassH0Diagram.plusFace 0))
    rw [Path.target, Path.source]

/-- H ends at the actual lower-left corner of A; its L endpoint equals Ppath(0). -/
def H (e : Bool) : Path (includeLaurent P p q (oldChartParameter P p q e 0))
    (chartStart P p q e 0) where
  toFun s := includeLaurent P p q (oldChartParameter P p q e s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := by
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.L BassH0Diagram.plusFace 1)) =
      includeLaurent P p q (Z P p q e (0, 0))
    rw [← first_movement_Z]
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.L BassH0Diagram.plusFace 1)) =
      includeLaurent P p q (parameter _ _
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace 0))
    rw [Path.target, Path.source]

/-- K is the actual Z row at p-polynomial time zero, with q-chart time unchanged. -/
abbrev K (e : Bool) := chartPath P p q e 0
/-- C17 is the actual P(0) cylinder, on its own sheet and ending at its own tip. -/
abbrev C17 (e : Bool) := firstCylinderPath P p q e 0

/-- The complete first-old null has the literal original right-nested four-piece word. -/
def oldNull (e : Bool) : Path (terminalStart P p q e) (tip P p q e) :=
  (D P p q e).trans ((H P p q e).trans (APath P p q e 0))

theorem oldNull_D (e : Bool) (s : I) : oldNull P p q e (lower s) = D P p q e s := by
  rw [oldNull, path_lower]
theorem oldNull_H (e : Bool) (s : I) :
    oldNull P p q e (upper (lower s)) = H P p q e s := by
  rw [oldNull, path_upper, path_lower]
theorem oldNull_K (e : Bool) (s : I) :
    oldNull P p q e (upper (upper (lower s))) = K P p q e s := by
  rw [oldNull, path_upper, path_upper, APath, path_lower]
theorem oldNull_C17 (e : Bool) (s : I) :
    oldNull P p q e (upper (upper (upper s))) = C17 P p q e s := by
  rw [oldNull, path_upper, path_upper, APath, path_upper]

/-- The complete ordinary H is the first literal half used by the C1 correction. -/
theorem ordinary_H (s : I) : H P p q false s =
    CoefficientBassPositiveC1ReassociationPieces.firstPath P p q s :=
  congrArg (includeLaurent P p q) (first_chart_parameter P p q false s)

/-- The complete ordinary K is the second literal half, with no reparameterization. -/
theorem ordinary_K (s : I) : K P p q false s =
    CoefficientBassPositiveC1ReassociationPieces.secondPath P p q s :=
  congrArg (includeLaurent P p q) (second_chart_parameter P p q false s)

/-- The complete ordinary cylinder uses the full polynomial endpoint equation. -/
theorem ordinary_C17 (s : I) : C17 P p q false s =
    CoefficientBassPositiveC1ReassociationPieces.thirdPath P p q s :=
  congrArg (fun y ↦ minusCylinder P p q (y, s)) (polynomial_endpoint P p q)

/-- The shifted first half keeps the actual commonUnit on every chart node. -/
theorem shifted_H (s : I) : H P p q true s =
    CoefficientBassPositiveC1ShiftedReassociationPieces.firstPath P p q s := by
  change includeLaurent P p q (oldChartParameter P p q true s) =
    includeLaurent P p q (mapParameter _ (parameter _ _
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s))))
  rw [mapParameter_parameter]
  exact congrArg (includeLaurent P p q) (first_chart_parameter P p q true s)

/-- The shifted second half retains the same q-chart clock and full product references. -/
theorem shifted_K (s : I) : K P p q true s =
    CoefficientBassPositiveC1ShiftedReassociationPieces.secondPath P p q s := by
  change includeLaurent P p q (Z P p q true (0, s)) =
    includeLaurent P p q (mapParameter _ (parameter _ _
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s))))
  rw [mapParameter_parameter]
  exact congrArg (includeLaurent P p q) (second_chart_parameter P p q true s)

/-- The shifted cylinder is independent and retains the plus tip. -/
theorem shifted_C17 (s : I) : C17 P p q true s =
    CoefficientBassPositiveC1ShiftedReassociationPieces.thirdPath P p q s :=
  congrArg (fun y ↦ plusCylinder P p q (y, s)) (polynomial_endpoint P p q)

/-- The ordinary tail is the exact target parentheses of the accepted correction. -/
theorem ordinary_tail (s : I) : ((H P p q false).trans (APath P p q false 0)) s =
    CoefficientBassPositiveC1CorrectedBoundary.correctedUpper P p q s :=
  map_trans_values id (H P p q false) (APath P p q false 0)
    (CoefficientBassPositiveC1ReassociationPieces.firstPath P p q)
    ((CoefficientBassPositiveC1ReassociationPieces.secondPath P p q).trans
      (CoefficientBassPositiveC1ReassociationPieces.thirdPath P p q))
    (ordinary_H P p q)
    (map_trans_values id (K P p q false) (C17 P p q false)
      (CoefficientBassPositiveC1ReassociationPieces.secondPath P p q)
      (CoefficientBassPositiveC1ReassociationPieces.thirdPath P p q)
      (ordinary_K P p q) (ordinary_C17 P p q)) s

/-- The shifted tail has the same exact nesting but its own full reference and tip. -/
theorem shifted_tail (s : I) : ((H P p q true).trans (APath P p q true 0)) s =
    CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedUpper P p q s :=
  map_trans_values id (H P p q true) (APath P p q true 0)
    (CoefficientBassPositiveC1ShiftedReassociationPieces.firstPath P p q)
    ((CoefficientBassPositiveC1ShiftedReassociationPieces.secondPath P p q).trans
      (CoefficientBassPositiveC1ShiftedReassociationPieces.thirdPath P p q))
    (shifted_H P p q)
    (map_trans_values id (K P p q true) (C17 P p q true)
      (CoefficientBassPositiveC1ShiftedReassociationPieces.secondPath P p q)
      (CoefficientBassPositiveC1ShiftedReassociationPieces.thirdPath P p q)
      (shifted_K P p q) (shifted_C17 P p q)) s

/-- The entire ordinary null equals the actual C1 endpoint null at the original null time. -/
theorem ordinary_null (s : I) : oldNull P p q false s =
    CoefficientBassPositiveC1SeedFace.nullMinus P p q (s, 1) := by
  change ((D P p q false).trans ((H P p q false).trans (APath P p q false 0))) s =
    ((CoefficientBassPositiveC1SeedFace.positiveMinus P p q).trans
      (CoefficientBassPositiveC1SeedFace.correctedMinus P p q)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact congrArg (includeLaurent P p q) (positive_ordinary P p q _)
  · exact (ordinary_tail P p q _).trans
      ((CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).at_one _).symm

/-- The entire shifted null equals C1 at unchanged time, still ending at the separate tip. -/
theorem shifted_null (s : I) : oldNull P p q true s =
    CoefficientBassPositiveC1SeedFace.nullPlus P p q (s, 1) := by
  change ((D P p q true).trans ((H P p q true).trans (APath P p q true 0))) s =
    ((CoefficientBassPositiveC1SeedFace.positivePlus P p q).trans
      (CoefficientBassPositiveC1SeedFace.correctedPlus P p q)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact congrArg (includeLaurent P p q) (positive_shifted P p q _)
  · exact (shifted_tail P p q _).trans
      ((CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).at_one _).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalNull
