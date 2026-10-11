/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNull

/-!
# Original supported-section relative-open null-track consumers

The genuine support property supplies the weak transformation. Its realized track retains
both original maps, the chosen point, independent structure time and the actual cone face.
No stability or full-open endpoint hypothesis enters these consumers.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.SupportedSectionOpenNull
open PerfectComplexes Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original evaluation sends each section cofibration to its actual relative-open cofibration. -/
theorem original_cofibration_map {s t : BoundedFlatAffineSections R} (a : s ⟶ t)
    (ha : (boundedFlatAffineSectionWaldhausen R).cof a) :
    (boundedFlatPerfectOpenWaldhausen j).cof ((boundedFlatAffineOriginalEvaluation R).map a) :=
  (boundedFlatAffineSectionOpenEvaluation_exact j).cofibration a ha

/-- The actual enlarged weak class keeps the original chosen section zero. -/
theorem original_section_zero :
    (boundedFlatAffineSectionOpenWaldhausen j).zero =
      (boundedFlatAffineSectionWaldhausen R).zero := rfl

/-- Weakness is proved from the actual original support witness of each original section. -/
theorem original_supported_weak_arrow (s : BoundedFlatAffineSupportedSections j) :
    (boundedFlatAffineSectionOpenWaldhausen j).weq
      ((boundedFlatAffineSupportedSectionZeroToOpen j).app s) :=
  boundedFlatAffineSupportedSectionZeroToOpen_weak j s

/-- The initial endpoint retains literal support inclusion and original coarse restriction. -/
theorem original_null_start (n : ℕ)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (0, x) =
      (boundedFlatAffineSectionOpenPrespectrumMap j).map n
        ((boundedFlatAffineSupportedSectionForgetPrespectrumMap j).map n x) :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy j).at_zero n x

/-- The final endpoint is the actual chosen point of the original relative-open section model. -/
theorem original_null_finish (n : ℕ)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (1, x) =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).point n :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy j).at_one n x

/-- The complete original basepoint line remains fixed at every nullhomotopy time. -/
theorem original_point_track (n : ℕ) (s : unitInterval) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).point n) =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).point n :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy j).at_point n s

/-- The original null time is independent of the original prespectrum structure parameter. -/
theorem original_independent_times (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level (n + 1)
        (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) t :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy j).comm n s x t

/-- The original ambient section map remains the actual target face of the descended cone. -/
theorem original_cone_face :
    mappingConeInclusion (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        boundedFlatAffineSupportedSectionOpenConeMap j =
      boundedFlatAffineSectionOpenPrespectrumMap j :=
  boundedFlatAffineSupportedSectionOpenConeMap_inclusion j

/-- Every original cylinder value is exactly the constructed support-restriction null track. -/
theorem original_cone_cylinder (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionOpenConeMap j).map n
        (ReducedMappingCone.cylinder
          ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)
          ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point n)
          ((boundedFlatAffineSupportedSectionForgetPrespectrumMap j).map n) (s, x)) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x) :=
  boundedFlatAffineSupportedSectionOpenConeMap_cylinder j n s x

end Quillen.Tests.SupportedSectionOpenNull
