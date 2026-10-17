/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairInitial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairNative
public import Quillen.Topology.Prespectrum.ConeSquareMovingNullEvaluation

/-! Native recovery of the original moving-null square on both genuine polynomial summands. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
open CommonReferenceNerve CoefficientBassRaw1PolynomialSourceAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The native moving square for the original coefficient Bass cone composition data. -/
abbrev initialNative := coneSquareNullMovingSquare
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientBassComparisonHomotopy P (p ≫ q))
  (boundedFlatCoefficientBassCompositeComparison P p q)
  (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q)
  (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
  (BassMWhole.comparisonSquare P p q)

/-- The original plus A restriction includes its terminal half pause. -/
theorem plus_paused_span (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
        (pointwisePrespectrumFamily
          (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
          (polynomialPausedPath P p q r) x) =
      (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
        (r, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) := by
  rw [polynomialPausedPath_native,
    boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inl]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [Homotopy.trans_lower_cell, Homotopy.trans_lower_cell]
    rfl
  · rw [Homotopy.trans_upper_cell, Homotopy.trans_upper_cell]
    rfl

/-- The plus interchange piece evaluates at the original A, with independent outer height. -/
theorem plusValue_last (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P p q n (last P (underToLaurent R) p q (r, h)) x =
      Quillen.ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P c).map n)
        (h, (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
          (r, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  have he := cylinder_native P (underToLaurent R) p q n (polynomialPausedPath P p q r) h x
  have hi := boundedFlatCoefficientBassPositiveConeInclusion_cylinder P c n h
    (pointwisePrespectrumFamily
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
      (polynomialPausedPath P p q r) x)
  have hh := (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P c).map n) he).trans hi
  exact hh.trans (congrArg (fun y ↦ Quillen.ReducedMappingCone.cylinder _ _
    ((boundedFlatCoefficientBassSquareComparison P c).map n) (h, y))
      (plus_paused_span P p q n r x))

/-- The entire original initial square is retained on the plus polynomial summand. -/
theorem plusValue_initial (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P p q n (initial P (underToLaurent R) p q (r, h)) x =
      (initialNative P p q).level n (r, (h, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  change plusValue P p q n
    (((firstSwap P (underToLaurent R) p q).trans (lastSwap P (underToLaurent R) p q)) (h, r)) x = _
  rw [ContinuousMap.Homotopy.trans_apply, initialNative, coneSquareNullMovingSquare_apply]
  split_ifs
  · exact plusValue_chartSquare P p q n r _ x
  · exact plusValue_last P p q n r _ x

/-- The original minus A restriction includes its terminal half pause. -/
theorem minus_paused_span (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
        (pointwisePrespectrumFamily
          (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
          (polynomialPausedPath P p q r) x) =
      (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
        (r, (HomotopyPushout.inr
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) := by
  rw [polynomialPausedPath_native,
    boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inr]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [Homotopy.trans_lower_cell, Homotopy.trans_lower_cell]
    rfl
  · rw [Homotopy.trans_upper_cell, Homotopy.trans_upper_cell]
    rfl

/-- The minus interchange piece evaluates at the original A, with independent outer height. -/
theorem minusValue_last (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P p q n (last P (underToLaurentInvert R) p q (r, h)) x =
      Quillen.ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P c).map n)
        (h, (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
          (r, (HomotopyPushout.inr
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  have he := cylinder_native P (underToLaurentInvert R) p q n (polynomialPausedPath P p q r) h x
  have hi := boundedFlatCoefficientBassNegativeConeInclusion_cylinder P c n h
    (pointwisePrespectrumFamily
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
      (polynomialPausedPath P p q r) x)
  have hh := (congrArg ((boundedFlatCoefficientBassNegativeConeInclusion P c).map n) he).trans hi
  exact hh.trans (congrArg (fun y ↦ Quillen.ReducedMappingCone.cylinder _ _
    ((boundedFlatCoefficientBassSquareComparison P c).map n) (h, y))
      (minus_paused_span P p q n r x))

/-- The entire original initial square is retained on the minus polynomial summand. -/
theorem minusValue_initial (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P p q n (initial P (underToLaurentInvert R) p q (r, h)) x =
      (initialNative P p q).level n (r, (h, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  change minusValue P p q n
    (((firstSwap P (underToLaurentInvert R) p q).trans
      (lastSwap P (underToLaurentInvert R) p q)) (h, r)) x = _
  rw [ContinuousMap.Homotopy.trans_apply, initialNative, coneSquareNullMovingSquare_apply]
  split_ifs
  · exact minusValue_chartSquare P p q n r _ x
  · exact minusValue_last P p q n r _ x

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
