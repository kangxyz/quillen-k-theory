/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCharts

/-! Semantic regressions for the original span identity and its two complete Bass chart faces. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalRawBassInputIdentity
variable (X : Scheme.{u})

/-- The constructed span identity finishes at the literal identity on every quotient point. -/
theorem entire_span_terminal (n : ℕ) (x : (span X).space n) :
    (InputIdentity.spanHomotopy X).level n (1, x) = x :=
  (InputIdentity.spanHomotopy X).at_one n x

/-- The original positive input-comparison face is retained at every degree-zero path time. -/
theorem positive_original_face_zero (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space 0) :
    (InputIdentity.comparisonPlusChart X).level 0 (0, (s, x)) =
      (inputComparisonHomotopy (𝟙 X)).level 0
        (s, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X))).map 0 x) :=
  (InputIdentity.comparisonPlusChart X).at_zero 0 s x

/-- The positive bottom side uses the original Laurent unit without a new constant segment. -/
theorem positive_laurent_face (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (InputIdentity.comparisonPlusChart X).level n (r, (0, x)) =
      (boundedFlatPerfectPrespectrumIdHomotopy (laurent.obj X)).level n
        (r, (boundedFlatPerfectPrespectrumMap (plus.app X)).map n x) :=
  (InputIdentity.comparisonPlusChart X).left n r x

/-- The inverse top side keeps its distinct Laurent chart and original polynomial unit time. -/
theorem inverse_polynomial_face (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (InputIdentity.comparisonMinusChart X).level n (r, (1, x)) =
      (boundedFlatPerfectPrespectrumMap (minus.app X)).map n
        ((boundedFlatPerfectPrespectrumIdHomotopy (polynomial.obj X)).level n (r, x)) :=
  (InputIdentity.comparisonMinusChart X).right n r x

/-- Both chart-square coordinates remain independent of the prespectrum structure time. -/
theorem inverse_chart_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (InputIdentity.comparisonMinusChart X).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (polynomial.obj X))).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        ((InputIdentity.comparisonMinusChart X).level n (r, (s, x))) t :=
  (InputIdentity.comparisonMinusChart X).comm n r s x t

end QuillenTest.GlobalRawBassInputIdentity
