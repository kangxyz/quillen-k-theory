/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeActualMixedFiller
public import Quillen.Topology.Prespectrum.NativeHomotopyCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierNativeEvaluation

/-! The prescribed first half of the original chosen composite cube's left face. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenChartEdge
open CommonReferenceNerve CoefficientBassCompositeActualLeftRoute
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- This is the original reversed middle comparison, with its full carrier references. -/
def edge : C(I × I, Carrier P p q) := (middle P p q).toContinuousMap

/-- The literal first half of the original route is the prescribed middle comparison. -/
theorem route_lower (r s : I) :
    route P p q (Quillen.NativePathCells.lower r, s) = edge P p q (r, s) := by
  change ((middle P p q).trans (first P p q)) (Quillen.NativePathCells.lower r, s) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change middle P p q (⟨2 * (Quillen.NativePathCells.lower r : ℝ), _⟩, s) =
      middle P p q (r, s)
    exact congrArg (fun t : I ↦ middle P p q (t, s))
      (Subtype.ext (by dsimp [Quillen.NativePathCells.lower]; ring))
  · rename_i hr
    exfalso
    apply hr
    change (r : ℝ) / 2 ≤ 1 / 2
    linarith [r.2.2]

/-- The original selected cube retains this whole left subface at the original half clock. -/
theorem chosen_left_half (r s : I) :
    (CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier
      ((0, Quillen.NativePathCells.lower r), s) = edge P p q (r, s) := by
  let B := CoefficientBassCompositeActualMixedFiller.boundary P p q
  have hf := B.extension_face (0, false)
    (CutOpenCarrier.RelativeBoundary.onFace (0, false)
      (CutOpenCarrier.RelativeBoundary.coordinates 0 (Quillen.NativePathCells.lower r) s) rfl)
  exact hf.trans (route_lower P p q r s)

/-- The complete initial seed is the original C0 target path. -/
theorem edge_zero (s : I) : edge P p q (0, s) = start P p q s :=
  (middle P p q).apply_zero s

/-- The complete final seed is the previously identified common midpoint word. -/
theorem edge_one (s : I) : edge P p q (1, s) = middlePath P p q s :=
  (middle P p q).apply_one s

/-- The first original tip is retained throughout the whole comparison. -/
theorem edge_bottom (r : I) : edge P p q (r, 0) = minusTip P p q :=
  (CoefficientBassPositiveLeftComparisons.middleComparison P p q).source (unitInterval.symm r)

/-- The distinct second tip is retained throughout the whole comparison. -/
theorem edge_top (r : I) : edge P p q (r, 1) = plusTip P p q :=
  (CoefficientBassPositiveLeftComparisons.middleComparison P p q).target (unitInterval.symm r)

/-- The native edge is the original reversed second-arrow seed track on the actual first image. -/
theorem edge_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (edge P p q (r, s)) x =
      Path.toContinuousMap ((boundedFlatCoefficientBassPositiveTransitionHomotopy P q).level n
        (unitInterval.symm r,
          (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s := by
  have h := CoefficientBassPositiveLeftComparisonNative.middle_comparison_transition
    P p q n (unitInterval.symm r) s x
  dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
  exact h

/-- The original full seed track is recovered on every native input and both original clocks. -/
theorem edge_full_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) n (edge P p q (r, s)) x) =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P q).symm.level n
        (r, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s :=
  (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P c).map n)
    (edge_native P p q n r s x)).trans
    (boundedFlatCoefficientBassPositiveTransitionHomotopy_factor P q n
      (unitInterval.symm r) s ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))

/-- The exact chosen edge enters the existing full augmentation for this same source model. -/
def augmentedEdge : C(I × I, CoefficientBassSeedCarrierAugmentation.space P p q) :=
  ⟨fun z ↦ CoefficientBassSeedCarrierAugmentation.originalMap P p q (edge P p q z),
    by fun_prop⟩

/-- The chosen cube's literal half face survives the full augmentation unchanged. -/
theorem augmented_chosen_left_half (r s : I) :
    CoefficientBassSeedCarrierAugmentation.originalMap P p q
      ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier
        ((0, Quillen.NativePathCells.lower r), s)) = augmentedEdge P p q (r, s) :=
  congrArg (CoefficientBassSeedCarrierAugmentation.originalMap P p q)
    (chosen_left_half P p q r s)

/-- The augmented chosen edge still evaluates to the original full reversed second seed. -/
theorem augmentedEdge_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    CoefficientBassSeedCarrierAugmentation.nativeEval P p q n (augmentedEdge P p q (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P q).symm.level n
          (r, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s :=
  (CoefficientBassSeedCarrierAugmentation.nativeEval_originalMap P p q n
    (edge P p q (r, s)) x).trans (edge_full_native P p q n r s x)

end Quillen.PerfectComplexes.CoefficientBassSeedChosenChartEdge
