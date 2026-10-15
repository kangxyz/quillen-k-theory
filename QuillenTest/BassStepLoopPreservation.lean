/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStepComparison

open Quillen.PerfectComplexes


/-!
# Original affine Bass-step loop-preservation consumers

The next actual parameter loop remains well-based. The original comparison
retains every stored cone-loop value, covers every target loop component, and
is bijective on the original negative stable groups. The geometric whole-square
compatibility track is kept explicit throughout.
-/

open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent

namespace QuillenTest.BassStepLoopPreservation

open Quillen

universe u

/-- Point HEP remains available after another actual loop of the original perfect Bass step. -/
theorem further_parameter_loop_point_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((parameterLooping (affineBassStep R)).point (n + 1)))) :=
  parameterLooping_point_homotopyExtensionProperty _ (n + 1) isClosed_singleton
    (affineBassStep_positivePoint_homotopyExtensionProperty R n)

variable (R : CommRingCat.{u})
  (H : Homotopy
    (boundedFlatBassSquareComparison R ≫
      exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R)))))
    (boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R) ≫
      bassSquareComparison R))

/-- Each loop coordinate is sent by the actual supplied whole-track cone comparison. -/
theorem original_cone_loop_value (n : ℕ)
    (γ : Path ((mappingCone (boundedFlatBassSquareComparison R)).point n)
      ((mappingCone (boundedFlatBassSquareComparison R)).point n)) (t : unitInterval) :
    Path.toContinuousMap ((boundedFlatPerfectBassStepMap R H).map n γ) t =
      (boundedFlatPerfectBassConeMap R H).map n (γ t) := rfl

/-- Every target Bass-step loop component is represented under the original map. -/
theorem original_target_loop_component (n : ℕ) (δ : (affineBassStep R).space (n + 1)) :
    ∃ γ : (boundedFlatAffineBassStep R).space (n + 1),
      Joined ((boundedFlatPerfectBassStepMap R H).map (n + 1) γ) δ :=
  (boundedFlatPerfectBassStepMap_positiveLevel_isWeakHomotopyEquivalence R H n).component_surjective
    δ

/-- The original negative stable-group map is bijective, with the geometric track explicit. -/
theorem original_negative_stable_bijective (n : ℕ) :
    Function.Bijective
      ((stableHomotopyFunctor (-((n : ℤ) + 1))).map (boundedFlatPerfectBassStepMap R H)) := by
  have := boundedFlatPerfectBassStepMap_isStableEquivalence R H (-((n : ℤ) + 1))
  exact ConcreteCategory.bijective_of_isIso _

end QuillenTest.BassStepLoopPreservation
