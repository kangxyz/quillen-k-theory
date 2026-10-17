/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenProjectionPaste

/-! The actual naturality-chart connecting face, retaining both selected cubes and all clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenChartSquare
open CoefficientBassSeedChosenPathCube CoefficientBassSeedChosenProjectionPaste
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
  {M N : Under R ⥤ Under R} (α : M ⟶ N)

/-- The full-reference chart square uses the literal two naturality factorizations. -/
def chartSquare :=
  square P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm

/-- Seed time remains the final coordinate of the whole scalar connecting face. -/
def face : C((I × I) × I,
    CoefficientBassPositiveC0CarrierSeed.Carrier P (M.map u) (α.app b)) :=
  (chartSquare P u α).parameter.uncurry

/-- The lower route retains both C0 pieces followed by the original second middle edge. -/
def lower :=
  (((D₀ P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm).cast
    (sharedSource
      (T₀ P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm)
      (T P (M.map u) (α.app b))
      (CoefficientBassSeedChosenPathTransport.shared_path P
        (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm)) rfl).symm.trans
    (surfacePath (CoefficientBassCompositeActualRightRoute.c0 P (M.map u) (α.app b))).symm).trans
    (surfacePath (CoefficientBassCompositeActualLeftRoute.middle P (M.map u) (α.app b)))

/-- The upper route retains the first edge and reversed/forward C1 pair at their half cuts. -/
def upper :=
  (CoefficientBassSeedChosenProjectionPaste.M P
    (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm).trans
    (((K₀ P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm).cast
      (sharedTarget
        (T₀ P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm)
        (T P (M.map u) (α.app b))
        (CoefficientBassSeedChosenPathTransport.shared_path P
          (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm)) rfl).symm.trans
      (surfacePath (CoefficientBassCompositeActualRightRoute.c1 P (M.map u) (α.app b))))

/-- The left side is the mapped original first cube's chosen middle half face. -/
def left := L P (α.app a) (N.map u) (M.map u) (α.app b) (α.naturality u).symm

/-- The right side is the original second cube's first comparison edge. -/
def right := surfacePath (CoefficientBassCompositeActualLeftRoute.first P (M.map u) (α.app b))

/-- The entire lower path is retained, before evaluation. -/
theorem face_zero (t s : I) : face P u α ((0, t), s) = lower P u α t s :=
  congrArg (fun γ ↦ γ s) ((chartSquare P u α).at_zero t)

/-- The entire upper path retains its original nested clocks. -/
theorem face_one (t s : I) : face P u α ((1, t), s) = upper P u α t s :=
  congrArg (fun γ ↦ γ s) ((chartSquare P u α).at_one t)

/-- The original chosen middle half face is the literal left edge. -/
theorem face_left (r s : I) : face P u α ((r, 0), s) = left P u α r s :=
  congrArg (fun γ ↦ γ s) ((chartSquare P u α).left r)

/-- The original second first-comparison face is the literal right edge. -/
theorem face_right (r s : I) : face P u α ((r, 1), s) = right P u α r s :=
  congrArg (fun γ ↦ γ s) ((chartSquare P u α).right r)

end Quillen.PerfectComplexes.CoefficientBassSeedChosenChartSquare
