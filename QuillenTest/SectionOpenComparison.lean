/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenComparison

/-!
# Original relative-open evaluation consumers

The original functor, coarse inverse, chosen zero, literal fine/coarse square, entire inverse
tracks and actual negative stable-class lift are retained. The endpoint is the relative model.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionOpenComparison

open Quillen
open PerfectComplexes Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The forward map is unchanged original evaluation followed by actual universe lifting. -/
theorem original_evaluation_functor :
    (boundedFlatAffineSectionOpenEvaluationModelMap j).functor =
      boundedFlatAffineOriginalEvaluation R ⋙ AsSmall.up := rfl

/-- The actual inverse preserves every supplied original relative weak map. -/
theorem original_inverse_weak {K L : BoundedFlatPerfect (Spec R)} (f : K ⟶ L)
    (hf : (boundedFlatPerfectOpenWaldhausen j).weq f) :
    (boundedFlatAffineSectionOpenWaldhausen j).weq
      ((boundedFlatAffineSectionEquivalence R).inverse.map f) :=
  (boundedFlatAffineSectionOpenEquivalence_inverse_exact j).weak f hf

/-- The actual original section zero maps to the inherited geometric coarse zero. -/
theorem original_zero_image :
    (boundedFlatAffineSectionSmallEquivalence R).functor.obj
        (boundedFlatAffineSectionOpenWaldhausen j).zero =
      (boundedFlatPerfectOpenWaldhausen j).smallModel.zero :=
  (boundedFlatAffineSectionOpenEvaluationModelMap j).zero

/-- Both original routes send the same original fine section point to the same coarse point. -/
theorem original_changeWeak_value (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j).map n
        ((boundedFlatAffineSectionOpenPrespectrumMap j).map n x) =
      (Waldhausen.Fibration.changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j)).map n
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map n x) :=
  congrArg (fun f => f.map n x) (boundedFlatAffineSectionOpenEvaluation_changeWeak j)

/-- The actual left inverse comparison ends at the unchanged source point. -/
theorem original_left_inverse_endpoint (n : ℕ)
    (x : (prespectrum (boundedFlatAffineSectionOpenModel j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationLeftHomotopy j).level n (1, x) = x :=
  (boundedFlatAffineSectionOpenEvaluationLeftHomotopy j).at_one n x

/-- The actual right inverse comparison ends at the unchanged target point. -/
theorem original_right_inverse_endpoint (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationRightHomotopy j).level n (1, x) = x :=
  (boundedFlatAffineSectionOpenEvaluationRightHomotopy j).at_one n x

/-- The whole left inverse track retains independent homotopy and structure parameters. -/
theorem original_inverse_independent_times (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSectionOpenModel j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationLeftHomotopy j).level (n + 1)
        (s, (prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n
        ((boundedFlatAffineSectionOpenEvaluationLeftHomotopy j).level n (s, x)) t :=
  (boundedFlatAffineSectionOpenEvaluationLeftHomotopy j).comm n s x t

/-- Each actual negative target class lifts under the unchanged original evaluation map. -/
theorem original_negative_class_lift (n : ℕ)
    (y : stableHomotopyGroup (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j))
      (-(n : ℤ) - 1)) :
    ∃ x, (stableHomotopyFunctor (-(n : ℤ) - 1)).map
      (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j) x = y := by
  let := boundedFlatAffineSectionOpenEvaluation_isStableEquivalence j (-(n : ℤ) - 1)
  exact (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor (-(n : ℤ) - 1)).map
      (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j))).surjective y

end QuillenTest.SectionOpenComparison
