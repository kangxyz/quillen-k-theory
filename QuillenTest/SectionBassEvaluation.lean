/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluation

/-! Actual Bass evaluation preserves original corners, complete cylinders and independent times. -/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent
open CommRingCat.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
  AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassEvaluation

open Quillen

/-- The original positive chart is literally evaluated before inclusion in the raw span. -/
theorem span_left (R : CommRingCat.{u}) :
    HomotopyPushout.inl (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R)) ≫
        boundedFlatAffineSectionBassSpanEvaluation R =
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R)) ≫
        HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The comparison starts at the literal strict comparison followed by original evaluation. -/
theorem original_source (R : CommRingCat.{u}) (n : ℕ)
    (x : (StrictSquare.span (boundedFlatAffineSectionBassSquare R)).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n (0, x) =
      (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n x :=
  (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).at_zero n x

/-- The other endpoint is the unchanged span evaluation followed by original raw Bass comparison. -/
theorem original_target (R : CommRingCat.{u}) (n : ℕ)
    (x : (StrictSquare.span (boundedFlatAffineSectionBassSquare R)).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n (1, x) =
      (boundedFlatAffineSectionBassSpanEvaluation R ≫ boundedFlatBassSquareComparison R).map n x :=
  (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).at_one n x

/-- The entire original double cylinder retains both independent comparison and cylinder times. -/
theorem original_cylinder (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassComparisonEvaluationHomotopy R).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R))
        (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R)) n (s, x)) =
      (boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare.level n (r, (s, x)) :=
  boundedFlatAffineSectionBassComparisonEvaluationHomotopy_cylinder R n r s x

/-- The same original square commutes with the independent prespectrum structure coordinate. -/
theorem three_times (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare.level (n + 1)
      (r, (s, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial R))))).structureMap n
        ((boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare.level n (r, (s, x))) t :=
  (boundedFlatAffineSectionBassEvaluationDescPasting R).toSquare.comm n r s x t

/-- The actual cone map retains original Laurent evaluation on its unchanged endpoint inclusion. -/
theorem original_cone_inclusion (R : CommRingCat.{u}) :
    mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)) ≫
        boundedFlatAffineSectionBassConeEvaluation R =
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison R) :=
  boundedFlatAffineSectionBassConeEvaluation_inclusion R

/-- The actual one-step map retains the original internal loop coordinate. -/
theorem original_loop (R : CommRingCat.{u}) (n : ℕ) (q : unitInterval)
    (γ : ((boundedFlatAffineSectionBassDiagram 1).obj R).space n) :
    (show Path ((mappingCone (boundedFlatBassSquareComparison R)).point n)
        ((mappingCone (boundedFlatBassSquareComparison R)).point n) from
      (boundedFlatAffineSectionBassStepEvaluation R).map n γ) q =
      (boundedFlatAffineSectionBassConeEvaluation R).map n
        ((show Path ((boundedFlatAffineSectionBassCone R).point n)
          ((boundedFlatAffineSectionBassCone R).point n) from γ) q) := rfl

end QuillenTest.SectionBassEvaluation
