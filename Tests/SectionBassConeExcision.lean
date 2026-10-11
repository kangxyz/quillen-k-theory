/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision

/-!
# Original coefficient and iterated-seed cone excision consumers

Every finite stage, arbitrary signed degree, original fiber basepoint and complete cone-cylinder
coordinate is retained. The first proved cutoff includes genuine target-component coverage.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.SectionBassConeExcision
open PerfectComplexes

/-- Arbitrary original cone-gap fiber points retain the full finite range across different stages.
-/
theorem original_cross_stage_gap_fiber (i j : ℕ) (R S : CommRingCat.{u})
    (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
      (boundedFlatAffineSectionBassDiagram j).obj S) (n k : ℕ) (hk : k < 2 * n + 2)
    (y : (homotopyFiber (mappingConeInclusion f)).space (n + max i j + 2))
    (z : HomotopyFiber ((mappingConeFiberComparison f).map (n + max i j + 2)) y) :
    Subsingleton (HomotopyGroup.Pi k
      (HomotopyFiber ((mappingConeFiberComparison f).map (n + max i j + 2)) y) z) :=
  IsHomotopyConnectedMap.fiber_subsingleton
    (boundedFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap i j R S f n) y z k hk

/-- Every unchanged coefficient map has invertible actual cone-gap maps in every signed degree.
-/
theorem original_coefficient_signed_map (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (mappingConeFiberComparison ((boundedFlatAffineSectionBassDiagram i).map f))) :=
  boundedFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence i f d

/-- Arbitrary negative groups of the original iterated Laurent seed retain the same comparison.
-/
theorem original_seed_negative_map (i : ℕ) (R : CommRingCat.{u}) (q : ℕ) :
    IsIso ((stableHomotopyFunctor (-(q : ℤ) - 1)).map
      (mappingConeFiberComparison ((boundedFlatAffineSectionBassTransition i).app R))) :=
  boundedFlatAffineSectionBass_transition_coneFiber_isStableEquivalence i R (-(q : ℤ) - 1)

/-- The stable comparison still projects to the literal original coefficient map. -/
theorem original_coefficient_projection (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    mappingConeFiberComparison ((boundedFlatAffineSectionBassDiagram i).map f) ≫
      homotopyFiberProjection
        (mappingConeInclusion ((boundedFlatAffineSectionBassDiagram i).map f)) =
          (boundedFlatAffineSectionBassDiagram i).map f :=
  mappingConeFiberComparison_projection _

/-- The canonical comparison keeps every original coefficient-cylinder time at every level. -/
theorem original_coefficient_cylinder (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (m : ℕ) (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space m) (t : unitInterval) :
    ((mappingConeFiberComparison ((boundedFlatAffineSectionBassDiagram i).map f)).map m x).val.2 t =
        ReducedMappingCone.cylinder
          (((boundedFlatAffineSectionBassDiagram i).obj R).point m)
          (((boundedFlatAffineSectionBassDiagram i).obj S).point m)
          (((boundedFlatAffineSectionBassDiagram i).map f).map m) (t, x) := rfl

/-- The first genuine cutoff covers all components of the original coefficient cone fiber. -/
theorem original_coefficient_cutoff_coverage (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (y : (homotopyFiber (mappingConeInclusion
      ((boundedFlatAffineSectionBassDiagram i).map f))).space (i + 2)) :
    ∃ x, Joined
      ((mappingConeFiberComparison ((boundedFlatAffineSectionBassDiagram i).map f)).map (i + 2) x)
      y := by
  have h := boundedFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
    i i R S ((boundedFlatAffineSectionBassDiagram i).map f) 0
  rw [Nat.zero_add, max_self] at h
  exact h.component_surjective y

end Quillen.Tests.SectionBassConeExcision
