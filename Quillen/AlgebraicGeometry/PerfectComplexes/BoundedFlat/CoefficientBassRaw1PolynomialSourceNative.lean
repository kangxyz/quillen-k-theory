/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceAttachment

/-! The actual two polynomial restrictions of A retain the original terminal half pause. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceAttachment
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete original left A restriction is the unchanged paused polynomial parameter. -/
theorem polynomialPausedPath_span_inl (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
      (pointwisePrespectrumFamily
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
        (polynomialPausedPath P p q r) x) := by
  rw [boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inl,
    polynomialPausedPath_native]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [Homotopy.trans_lower_cell, Homotopy.trans_lower_cell]
    rfl
  · rw [Homotopy.trans_upper_cell, Homotopy.trans_upper_cell]
    rfl

/-- The separate original right A restriction retains its own target inclusion. -/
theorem polynomialPausedPath_span_inr (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
    (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
      (pointwisePrespectrumFamily
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
        (polynomialPausedPath P p q r) x) := by
  rw [boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inr,
    polynomialPausedPath_native]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [Homotopy.trans_lower_cell, Homotopy.trans_lower_cell]
    rfl
  · rw [Homotopy.trans_upper_cell, Homotopy.trans_upper_cell]
    rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceAttachment
