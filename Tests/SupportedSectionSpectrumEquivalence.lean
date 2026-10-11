/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionSpectrumEquivalence

/-!
# Original normalized supported evaluation consumers

The actual normalization at the original section zero is retained, together with the unchanged
raw evaluation on arbitrary section arrows. Both inverse homotopies retain their endpoints and
independent structure/homotopy times. All source components, level zero and negative stable degrees
are tested without new connectivity or comparison assumptions.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace Quillen.Tests.SupportedSectionSpectrumEquivalence
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- On the actual section zero, normalization is the canonical zero-object isomorphism. -/
theorem original_zero_normalization :
    ((boundedFlatAffineSupportedSectionEvaluationNormalizationIso j).app
        (boundedFlatAffineSupportedSectionWaldhausen j).zero).hom ≫
        eqToHom (boundedFlatAffineSupportedSectionEvaluationModelMap j).zero =
      (((boundedFlatAffineSupportedSectionSmallEquivalence_exact j).zero
        (boundedFlatAffineSupportedSectionWaldhausen j).isZero).iso
        (boundedFlatPerfectSupportedWaldhausen j).smallModel.isZero).hom :=
  (boundedFlatPerfectSupportedWaldhausen j).smallModel.isZero.eq_of_tgt _ _

/-- The specified comparison retains the original evaluation of an arbitrary section arrow. -/
theorem original_evaluation_normalization_naturality
    {s t : BoundedFlatAffineSupportedSections j} (a : s ⟶ t) :
    (AsSmall.up.map ((boundedFlatAffineSupportedEvaluation j).map a)) ≫
        (boundedFlatAffineSupportedSectionEvaluationModelIso j).hom.app t =
      (boundedFlatAffineSupportedSectionEvaluationModelIso j).hom.app s ≫
        (boundedFlatAffineSupportedSectionEvaluationModelMap j).functor.map a :=
  (boundedFlatAffineSupportedSectionEvaluationModelIso j).hom.naturality a

/-- At level zero the actual left inverse track begins at the original composite. -/
theorem original_level_zero_left_inverse_start
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space 0) :
    (boundedFlatAffineSupportedSectionEvaluationLeftHomotopy j).level 0 (0, x) =
      (boundedFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map 0
        ((boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j).map 0 x) :=
  (boundedFlatAffineSupportedSectionEvaluationLeftHomotopy j).at_zero 0 x

/-- The actual right inverse ends at every original geometric level point. -/
theorem original_right_inverse_end (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedFlatAffineSupportedSectionEvaluationRightHomotopy j).level n (1, x) = x :=
  (boundedFlatAffineSupportedSectionEvaluationRightHomotopy j).at_one n x

/-- Homotopy time and original structure time remain independent. -/
theorem original_left_inverse_structure_track (n : ℕ) (r t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionEvaluationLeftHomotopy j).level (n + 1)
        (r, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n
        ((boundedFlatAffineSupportedSectionEvaluationLeftHomotopy j).level n (r, x)) t :=
  (boundedFlatAffineSupportedSectionEvaluationLeftHomotopy j).comm n r x t

/-- Every finite homotopy degree is detected at an arbitrary original source-level point. -/
theorem original_all_component_bijectivity (n k : ℕ)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    Function.Bijective (homotopyGroupMap (N := Fin k)
      ((boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n) (x := x) rfl) := by
  have h := boundedFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence j n
  exact h.homotopy_bijective x k

/-- The same original normalized comparison reaches every target component, including level zero.
-/
theorem original_target_component_coverage (n : ℕ)
    (y : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    ∃ x, Joined ((boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n x) y := by
  have h := boundedFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence j n
  exact h.component_surjective y

/-- Negative stable groups use the unchanged normalized original prespectrum comparison. -/
theorem original_negative_stable_map (k : ℕ) :
    IsIso ((LoopPrespectrum.stableHomotopyFunctor (-(k : ℤ) - 1)).map
      (boundedFlatAffineSupportedSectionEvaluationPrespectrumMap j)) :=
  boundedFlatAffineSupportedSectionEvaluation_isStableEquivalence j _

end Quillen.Tests.SupportedSectionSpectrumEquivalence
