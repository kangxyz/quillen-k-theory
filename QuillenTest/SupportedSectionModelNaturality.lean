/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionModelNaturality

/-!
# Actual supported coefficient comparison consumers

Both original ring and open-side arrows remain explicit. The geometric Model arrow is exactly
the original pair pullback with canonical zero normalization. Both evaluation normalizations
remain in the actual comparison; the whole track retains its endpoints, point and independent
structure parameter, including the original level zero.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace QuillenTest.SupportedSectionModelNaturality

open Quillen
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The original geometric open-pair pullback and its actual zero iso define the Model functor. -/
theorem original_geometric_coefficient_functor :
    (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor =
      smallModelFunctor (Quillen.rebaseFunctor
        (boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h))
        (boundedFlatPerfectSupportedWaldhausen j).zero
        (boundedFlatPerfectSupportedWaldhausen j').zero
        (((boundedFlatPerfectSupportedPullback_exact
          (boundedFlatAffineSupportedPairSquare j j' f l h)).zero
            (boundedFlatPerfectSupportedWaldhausen j).isZero).iso
              (boundedFlatPerfectSupportedWaldhausen j').isZero)) := rfl

/-- The actual normalized geometric coefficient map retains the specified target zero. -/
theorem original_geometric_coefficient_zero :
    (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor.obj
        (modelOf (boundedFlatPerfectSupportedWaldhausen j)).waldhausen.zero =
      (modelOf (boundedFlatPerfectSupportedWaldhausen j')).waldhausen.zero :=
  (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).zero

/-- The comparison commutes with the unchanged original supported section arrow. -/
theorem original_coefficient_comparison_naturality
    {s t : BoundedFlatAffineSupportedSections j} (a : s ⟶ t) :
    (boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedFlatAffineSupportedSectionEvaluationModelMap j').functor.map a ≫
        (boundedFlatAffineSupportedSectionEvaluationCoefficientIso j j' f l h).hom.app t =
      (boundedFlatAffineSupportedSectionEvaluationCoefficientIso j j' f l h).hom.app s ≫
        (boundedFlatAffineSupportedSectionEvaluationModelMap j ≫
          boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h).functor.map a :=
  (boundedFlatAffineSupportedSectionEvaluationCoefficientIso j j' f l h).hom.naturality a

/-- The original level-zero track begins at coefficient restriction followed by evaluation. -/
theorem original_level_zero_source
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space 0) :
    (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).level 0 (0, x) =
      (boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j').map 0
        ((boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).map 0 x) :=
  (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).at_zero 0 x

/-- The target endpoint retains original normalized evaluation then original pair pullback. -/
theorem original_target_endpoint (n : ℕ)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).level n (1, x) =
      (prespectrumMap (boundedFlatAffineSupportedOriginalCoefficientModelMap j j' f l h)).map n
        ((boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n x) :=
  (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).at_one n x

/-- The actual chosen point is fixed throughout the entire original comparison. -/
theorem original_point_track (n : ℕ) (s : unitInterval) :
    (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).level n
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).point n) =
      (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j')).point n :=
  (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).at_point n s

/-- Comparison time and original structure time remain independent at every level. -/
theorem original_structure_track (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).level (n + 1)
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j')).structureMap n
        ((boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).level n
          (s, x)) t :=
  (boundedFlatAffineSupportedSectionEvaluationCoefficientHomotopy j j' f l h).comm n s x t

end QuillenTest.SupportedSectionModelNaturality
