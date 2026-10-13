/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeExcision

/-!
# Original Bass telescope cone-excision and signed-boundary consumers

The unchanged coefficient arrow, cone inclusion, canonical fiber comparison, arbitrary negative
degrees and finite-stage boundary maps are retained without any whole-telescope connectivity
assumption. Every actual source point and full cylinder time remains available.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.BassTelescopeConeExactness

open Quillen
open PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The unchanged telescope comparison induces an isomorphism in every original negative degree.
-/
theorem original_negative_cone_fiber_map (q : ℕ) :
    IsIso ((stableHomotopyFunctor (-(q : ℤ) - 1)).map
      (mappingConeFiberComparison (boundedFlatAffineSectionBassTelescopeMap f))) :=
  boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f (-(q : ℤ) - 1)

/-- Every actual telescope point keeps its entire original reduced cone path in the comparison.
-/
theorem original_telescope_cylinder (k : ℕ)
    (x : (boundedFlatAffineSectionBassTelescope R).space k) (t : unitInterval) :
    ((mappingConeFiberComparison (boundedFlatAffineSectionBassTelescopeMap f)).map k x).val.2 t =
      ReducedMappingCone.cylinder ((boundedFlatAffineSectionBassTelescope R).point k)
        ((boundedFlatAffineSectionBassTelescope S).point k)
        ((boundedFlatAffineSectionBassTelescopeMap f).map k) (t, x) := rfl

/-- The actual original coefficient kernel is precisely the image of the same signed boundary.
-/
theorem original_signed_coefficient_kernel (d : ℤ)
    (x : stableHomotopyGroup (boundedFlatAffineSectionBassTelescope R) d) :
    (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f) x = 0 ↔
      ∃ y, boundedFlatAffineSectionBassTelescopeConeConnecting f d y = x :=
  (boundedFlatAffineSectionBassTelescopeConeLongExactSequence f d).2.1 x

/-- The unchanged cone inclusion detects the image of the original telescope coefficient map.
-/
theorem original_signed_cone_inclusion_kernel (d : ℤ)
    (y : stableHomotopyGroup (boundedFlatAffineSectionBassTelescope S) d) :
    (stableHomotopyFunctor d).map
      (mappingConeInclusion (boundedFlatAffineSectionBassTelescopeMap f)) y = 0 ↔
      ∃ x, (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f) x = y :=
  (boundedFlatAffineSectionBassTelescopeConeLongExactSequence f d).2.2 y

/-- The actual boundary kernel is the original cone inclusion's image in its shifted signed degree.
-/
theorem original_signed_boundary_kernel (d : ℤ)
    (z : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) (d + 1)) :
    boundedFlatAffineSectionBassTelescopeConeConnecting f d z = 0 ↔
      ∃ y, (stableHomotopyFunctor (d + 1)).map
        (mappingConeInclusion (boundedFlatAffineSectionBassTelescopeMap f)) y = z :=
  (boundedFlatAffineSectionBassTelescopeConeLongExactSequence f d).1 z

/-- Every original finite-stage cone class keeps exactly its existing signed boundary value. -/
theorem original_finite_stage_boundary (d : ℤ) (i : ℕ)
    (z : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSectionBassDiagram i).map f)) (d + 1)) :
    boundedFlatAffineSectionBassTelescopeConeConnecting f d
      ((stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSectionBassConeStageMap f i) z) =
      (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassTelescopeInclusion i).app R)
        (stableMappingConeConnecting ((boundedFlatAffineSectionBassDiagram i).map f)
          (boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f) d z) :=
  ConcreteCategory.congr_hom (boundedFlatAffineSectionBassTelescopeConeConnecting_stage f d i) z

/-- After the unchanged comparison, the boundary is literally the original signed fiber boundary.
-/
theorem original_fiber_boundary_value (d : ℤ)
    (z : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) (d + 1)) :
    (stableHomotopyFunctor d).map
      (mappingConeFiberComparison (boundedFlatAffineSectionBassTelescopeMap f))
      (boundedFlatAffineSectionBassTelescopeConeConnecting f d z) =
        stableFiberConnecting (mappingConeInclusion (boundedFlatAffineSectionBassTelescopeMap f))
          d z :=
  ConcreteCategory.congr_hom (stableMappingConeConnecting_comparison
    (boundedFlatAffineSectionBassTelescopeMap f)
    (boundedFlatAffineSectionBassTelescope_coneFiber_isStableEquivalence f) d) z

end QuillenTest.BassTelescopeConeExactness
