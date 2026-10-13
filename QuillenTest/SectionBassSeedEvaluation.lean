/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeedEvaluation

/-! The original strict and raw Bass seeds retain their actual loop maps and independent times. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassSeedEvaluation

open Quillen

/-- The first homotopy endpoint is the unchanged strict seed followed by actual step evaluation. -/
theorem original_source (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).level n (0, x) =
      (boundedFlatAffineSectionBassSeedMap R ≫
        boundedFlatAffineSectionBassStepEvaluation R).map n x :=
  (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).at_zero n x

/-- The other endpoint is unchanged evaluation followed by the original geometric Bass seed. -/
theorem original_target (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).level n (1, x) =
      (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
        boundedFlatAffineBassTransition R).map n x :=
  (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).at_one n x

/-- Every original internal loop coordinate is the actual conjugated-loop relative comparison. -/
theorem original_loop (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (show Path ((mappingCone (boundedFlatBassSquareComparison R)).point n)
        ((mappingCone (boundedFlatBassSquareComparison R)).point n) from
      (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).level n (r, x)) s =
      (Quillen.PerfectComplexes.SectionBassSeedEvaluation.conjugateComparison R).level n
        (r, (s, x)) := rfl

/-- The same original loop comparison retains an independent spectrum-structure parameter. -/
theorem three_times (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (Quillen.PerfectComplexes.SectionBassSeedEvaluation.conjugateComparison R).level (n + 1)
      (r, (s, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (mappingCone (boundedFlatBassSquareComparison R)).structureMap n
        ((Quillen.PerfectComplexes.SectionBassSeedEvaluation.conjugateComparison R).level n
          (r, (s, x))) t :=
  (Quillen.PerfectComplexes.SectionBassSeedEvaluation.conjugateComparison R).comm n r s x t

/-- The original degree-zero loop space is included, with its independent internal loop time. -/
theorem zero_level_loop (R : CommRingCat.{u}) (r s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (show Path ((mappingCone (boundedFlatBassSquareComparison R)).point 0)
        ((mappingCone (boundedFlatBassSquareComparison R)).point 0) from
      (boundedFlatAffineSectionBassSeedEvaluationHomotopy R).level 0 (r, x)) s =
      (Quillen.PerfectComplexes.SectionBassSeedEvaluation.conjugateComparison R).level 0
        (r, (s, x)) := rfl

end QuillenTest.SectionBassSeedEvaluation
