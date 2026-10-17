/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenChartSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierNativeEvaluation

/-! Place the exact selected-cube chart square in the existing full augmented carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenChartAugmentation
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
  {M N : Under R ⥤ Under R} (α : M ⟶ N)

/-- The actual full-carrier face is the original-sheet inclusion of the checked scalar face. -/
def face : C((I × I) × I, CoefficientBassSeedCarrierAugmentation.space P (M.map u) (α.app b)) :=
  (CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b)).comp
    (CoefficientBassSeedChosenChartSquare.face P u α)

/-- The whole lower carrier path is retained by the full augmentation. -/
theorem face_zero (t s : I) : face P u α ((0, t), s) =
    CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b)
      (CoefficientBassSeedChosenChartSquare.lower P u α t s) :=
  congrArg (CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b))
    (CoefficientBassSeedChosenChartSquare.face_zero P u α t s)

/-- The upper original first-edge/C1-pair word keeps every original half cut. -/
theorem face_one (t s : I) : face P u α ((1, t), s) =
    CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b)
      (CoefficientBassSeedChosenChartSquare.upper P u α t s) :=
  congrArg (CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b))
    (CoefficientBassSeedChosenChartSquare.face_one P u α t s)

/-- The original chosen middle half face is included without changing its parameter. -/
theorem face_left (r s : I) : face P u α ((r, 0), s) =
    CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b)
      (CoefficientBassSeedChosenChartSquare.left P u α r s) :=
  congrArg (CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b))
    (CoefficientBassSeedChosenChartSquare.face_left P u α r s)

/-- The second first-comparison edge is included as the literal right side. -/
theorem face_right (r s : I) : face P u α ((r, 1), s) =
    CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b)
      (CoefficientBassSeedChosenChartSquare.right P u α r s) :=
  congrArg (CoefficientBassSeedCarrierAugmentation.originalMap P (M.map u) (α.app b))
    (CoefficientBassSeedChosenChartSquare.face_right P u α r s)

/-- Every augmented face value recovers the fixed full-cone support inclusion. -/
theorem face_native (n : ℕ) (r t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, M.obj a)))).space n) :
    CoefficientBassSeedCarrierAugmentation.nativeEval P (M.map u) (α.app b) n
      (face P u α ((r, t), s)) x =
    (boundedFlatCoefficientBassPositiveConeInclusion P (N.obj b)).map n
      (CutOpenCarrier.nativeEval
        (polynomialReference P (M.map u) (α.app b)) (chartMap P (c := N.obj b))
        (laurentReference P (M.map u) (α.app b))
        (ordinaryAnchor P (M.map u) (α.app b))
        (LaurentUnitReferenceSpecialization.shiftedAnchor P (M.map u) (α.app b)) n
        (CoefficientBassSeedChosenChartSquare.face P u α ((r, t), s)) x) :=
  CoefficientBassSeedCarrierAugmentation.nativeEval_originalMap P (M.map u) (α.app b) n
    (CoefficientBassSeedChosenChartSquare.face P u α ((r, t), s)) x

end Quillen.PerfectComplexes.CoefficientBassSeedChosenChartAugmentation
