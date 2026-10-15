/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSpanStableGroups

/-!
# Original polynomial-span and raw Bass excision consumers

These consumers retain the two geometric chart maps, the original signed cone boundary, and
unchanged negative-degree fiber representatives. All topology and excision inputs are discharged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.BoundedFlatBassSpanStableGroups

open Quillen
variable (R : CommRingCat.{u})

/-- The unchanged raw Bass comparison sends every span class into the two actual chart images. -/
theorem original_two_chart_image
    (z : stableHomotopyGroup (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))) 0) :
    ∃ x : stableHomotopyGroup (originalPrespectrum
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))) 0,
    ∃ y : stableHomotopyGroup (originalPrespectrum
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))) 0,
      (stableHomotopyFunctor 0).map (boundedFlatBassSquareComparison R) z =
        (stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentPlus R)) x +
        (stableHomotopyFunctor 0).map (boundedFlatPerfectPrespectrumMap (laurentMinus R)) y := by
  obtain ⟨x, y, h⟩ := boundedFlatBassSpan_stable_zero_generate R z
  refine ⟨x, y, ?_⟩
  have he := congrArg ((stableHomotopyFunctor 0).map (boundedFlatBassSquareComparison R)) h
  simp only [map_add, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    boundedFlatBassSquareComparison, HomotopyPushout.inl_desc, HomotopyPushout.inr_desc] at he
  exact he.symm

/-- Every actual negative span class is zero, with the signed degree retained literally. -/
theorem original_negative_span_class_zero (n : ℕ)
    (z : stableHomotopyGroup (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))) (-(n : ℤ) - 1)) : z = 0 :=
  (boundedFlatBassSpan_stable_neg_subsingleton R (-(n : ℤ) - 1) (by omega)).elim _ _

/-- The genuine original cone inclusion kills the image of every unchanged signed span map. -/
theorem original_cone_inclusion_kills_span_image (d : ℤ)
    (z : stableHomotopyGroup (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))) d) :
    (stableHomotopyFunctor d).map (mappingConeInclusion (boundedFlatBassSquareComparison R))
      ((stableHomotopyFunctor d).map (boundedFlatBassSquareComparison R) z) = 0 :=
  (stableMappingCone_exact_target (boundedFlatBassSquareComparison R)
    (boundedFlatBassSquareComparison_coneFiber_isStableEquivalence R) d _).mpr ⟨z, rfl⟩

/-- The actual signed cone boundary into the original negative-one span group vanishes. -/
theorem original_raw_negative_one_boundary_zero
    (z : stableHomotopyGroup (mappingCone (boundedFlatBassSquareComparison R)) ((-1 : ℤ) + 1)) :
    stableMappingConeConnecting (boundedFlatBassSquareComparison R)
      (boundedFlatBassSquareComparison_coneFiber_isStableEquivalence R) (-1) z = 0 :=
  (boundedFlatBassSpan_stable_neg_subsingleton R (-1) (by omega)).elim _ _

/-- Original negative-degree fiber classes come from the unchanged cone-fiber comparison. -/
theorem original_negative_fiber_representative (n : ℕ)
    (z : stableHomotopyGroup
      (homotopyFiber (mappingConeInclusion (boundedFlatBassSquareComparison R))) (-(n : ℤ) - 1)) :
    ∃ x : stableHomotopyGroup (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))) (-(n : ℤ) - 1),
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map
        (mappingConeFiberComparison (boundedFlatBassSquareComparison R)) x = z := by
  let := boundedFlatBassSquareComparison_coneFiber_isStableEquivalence R (-(n : ℤ) - 1)
  exact (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor (-(n : ℤ) - 1)).map
      (mappingConeFiberComparison (boundedFlatBassSquareComparison R)))).surjective z

/-- All actual points, rather than just the chosen point, satisfy the required finite range. -/
theorem original_span_all_point_classes (n : ℕ)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).space (n + 2))
    (a b : HomotopyGroup.Pi (n + 1) ((HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).space (n + 2)) x) : a = b :=
  (boundedFlatBassSpan_homotopyGroup_subsingleton_at R n (n + 1) (by omega) x).elim _ _

end QuillenTest.BoundedFlatBassSpanStableGroups
