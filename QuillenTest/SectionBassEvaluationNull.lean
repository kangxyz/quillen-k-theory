/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationNull

/-! Original section-evaluation null tracks retain endpoints and independent cylinder times. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.SectionBassEvaluationNull
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassEvaluationNull

open Quillen

/-- The initial relative face is the unchanged strict null followed by actual cone evaluation. -/
theorem original_source (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (originalNullComparison R).level n (0, (s, x)) =
      (boundedFlatAffineSectionBassConeEvaluation R).map n
        ((boundedFlatAffineSectionBassNullHomotopy R).level n (s, x)) :=
  ((originalNullComparison R).level n).apply_zero (s, x)

/-- The final face retains the actual Laurent coefficient track and original raw null. -/
theorem original_target (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (originalNullComparison R).level n (1, (s, x)) =
      ((laurentMovement R).trans (originalNewNull R)).level n (s, x) :=
  ((originalNullComparison R).level n).apply_one (s, x)

/-- The raw null is preceded by the unchanged original base evaluation at every coordinate. -/
theorem original_raw_null (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (originalNewNull R).level n (s, x) =
      (boundedFlatBassLaurentNullHomotopy R).level n
        (s, (boundedFlatAffineSectionEvaluationPrespectrumMap R).map n x) := rfl

/-- Comparison, null-cylinder and prespectrum structure coordinates remain independent. -/
theorem three_times (R : CommRingCat.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (originalNullComparison R).level (n + 1)
      (r, (s, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
      (mappingCone (boundedFlatBassSquareComparison R)).structureMap n
        ((originalNullComparison R).level n (r, (s, x))) t :=
  (originalNullComparison R).comm n r s x t

/-- The geometric source-leg square uses the literal original cone coordinate. -/
theorem source_leg_square (R : CommRingCat.{u}) (n : ℕ) (r s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassSourceLegEvaluationConeSquare R).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatBassSquareComparison R)).level n
        (s, (boundedFlatAffineSectionBassSourceLegEvaluationHomotopy R).level n (r, x)) :=
  boundedFlatAffineSectionBassSourceLegEvaluationConeSquare_apply R n r s x

end QuillenTest.SectionBassEvaluationNull
