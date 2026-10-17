/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenPathTransport

/-! Pointwise native recovery of the original selected cube and its full carrier transport. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenCubeNative
open CommonReferenceNerve CoefficientBassCompositeActualLeftRoute
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)

/-- The original supported relative comparison evaluates the same selected cube at all times. -/
theorem supported_native (n : ℕ) (r t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n
      ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier ((r, t), s)) x =
    Path.toContinuousMap
      ((CoefficientBassCompositeActualMixedFiller.supportedComparison P p q).level n
        (r, (t, x))) s := rfl

/-- Original whole-cone recovery uses the fixed positive support inclusion. -/
theorem original_native (n : ℕ) (r t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) n
        ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier ((r, t), s)) x) =
    Path.toContinuousMap
      ((CoefficientBassCompositeActualMixedFiller.originalComparison P p q).level n
        (r, (t, x))) s := by
  exact congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P c).map n)
    (supported_native P p q n r t s x)

end Quillen.PerfectComplexes.CoefficientBassSeedChosenCubeNative
