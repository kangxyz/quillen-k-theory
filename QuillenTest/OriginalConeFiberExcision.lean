/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-!
# Original geometric and strict-section consumers of genuine stable cone excision

These consumers use unchanged coefficient maps, literal cone cylinders, arbitrary fiber points
and every signed degree. All finite connectivity and point HEP assumptions are discharged by
the actual original S-models; no cone exactness or replacement-map premise is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.OriginalConeFiberExcision

open Quillen

/-- The actual strict-section coefficient arrow has genuine stable cone-to-fiber excision. -/
theorem actual_section_coefficient_stable {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsStableEquivalence
      (mappingConeFiberComparison (boundedFlatAffineSectionPrespectrumFunctor.map f)) :=
  prespectrum_mappingConeFiberComparison_isStableEquivalence _

/-- The original normalized geometric coefficient arrow satisfies the same stable theorem. -/
theorem original_coefficient_stable {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsStableEquivalence
      (mappingConeFiberComparison (boundedFlatPerfectPrespectrumMap (Spec.map f))) :=
  originalPrespectrum_mappingConeFiberComparison_isStableEquivalence
    (boundedFlatPerfectWaldhausen (Spec R)) (boundedFlatPerfectWaldhausen (Spec S)) _

/-- In particular the exact original comparison is invertible in every negative stable degree. -/
theorem original_coefficient_negative_degree {R S : CommRingCat.{u}} (f : R ⟶ S) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (mappingConeFiberComparison (boundedFlatPerfectPrespectrumMap (Spec.map f)))) :=
  original_coefficient_stable f _

/-- Finite excision covers every target point and every original fiber point in its full range. -/
theorem actual_section_all_fiber_points {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n k : ℕ) (hk : k < 2 * n)
    (y : (homotopyFiber (mappingConeInclusion
      (boundedFlatAffineSectionPrespectrumFunctor.map f))).space (n + 1))
    (z : HomotopyFiber ((mappingConeFiberComparison
      (boundedFlatAffineSectionPrespectrumFunctor.map f)).map (n + 1)) y) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber ((mappingConeFiberComparison
      (boundedFlatAffineSectionPrespectrumFunctor.map f)).map (n + 1)) y) z) :=
  (prespectrum_mappingConeFiberComparison_isHomotopyConnectedMap
    (boundedFlatAffineSectionPrespectrumFunctor.map f) n).fiber_subsingleton y z k hk

/-- The first positive level includes component coverage, even though its finite range is zero. -/
theorem actual_section_first_level_coverage {R S : CommRingCat.{u}} (f : R ⟶ S)
    (y : (homotopyFiber (mappingConeInclusion
      (boundedFlatAffineSectionPrespectrumFunctor.map f))).space 1) :
    ∃ x, Joined ((mappingConeFiberComparison
      (boundedFlatAffineSectionPrespectrumFunctor.map f)).map 1 x) y :=
  (prespectrum_mappingConeFiberComparison_isHomotopyConnectedMap
    (boundedFlatAffineSectionPrespectrumFunctor.map f) 0).component_surjective y

/-- The stable comparison still projects exactly to the unchanged original coefficient arrow. -/
theorem original_coefficient_projection {R S : CommRingCat.{u}} (f : R ⟶ S) :
    mappingConeFiberComparison (boundedFlatPerfectPrespectrumMap (Spec.map f)) ≫
      homotopyFiberProjection
        (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (Spec.map f))) =
        boundedFlatPerfectPrespectrumMap (Spec.map f) :=
  mappingConeFiberComparison_projection _

/-- Every time in the original cone path is retained, independently of level and coefficient. -/
theorem actual_section_original_path {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) (t : unitInterval) :
    ((mappingConeFiberComparison
      (boundedFlatAffineSectionPrespectrumFunctor.map f)).map n x).1.2 t =
      ReducedMappingCone.cylinder ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point n)
        ((boundedFlatAffineSectionPrespectrumFunctor.obj S).point n)
        ((boundedFlatAffineSectionPrespectrumFunctor.map f).map n) (t, x) := rfl

end QuillenTest.OriginalConeFiberExcision
