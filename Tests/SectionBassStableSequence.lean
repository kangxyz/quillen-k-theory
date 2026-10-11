/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassStableSequence

/-!
# Original iterated Laurent-seed stable cone sequence consumers

The original iterated transition, its actual coefficient naturality square and every signed
stable degree remain visible. These consumers use the proved all-stage excision, with no
connectivity, point HEP, seed-compatibility or cofiber-exactness premise.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.SectionBassStableSequence

/-- The literal coefficient naturality square of the original iterated Laurent seed. -/
def actualTransitionSquare (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Arrow.mk ((boundedFlatAffineSectionBassTransition i).app R) ⟶
      Arrow.mk ((boundedFlatAffineSectionBassTransition i).app S) :=
  Arrow.homMk ((boundedFlatAffineSectionBassDiagram i).map f)
    ((boundedFlatAffineSectionBassDiagram (i + 1)).map f)
    ((boundedFlatAffineSectionBassTransition i).naturality f)

/-- Negative-degree kernel classes lift along the unchanged actual iterated Laurent seed. -/
theorem original_transition_negative_kernel_lift (i : ℕ) (R : CommRingCat.{u}) (k : ℕ)
    (x : stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
      (-(Int.ofNat k + 1)))
    (hx : (stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (mappingConeInclusion ((boundedFlatAffineSectionBassTransition i).app R)) x = 0) :
    ∃ y, (stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((boundedFlatAffineSectionBassTransition i).app R) y = x :=
  ((boundedFlatAffineSectionBassMap_longExactSequence i (i + 1) R R
    ((boundedFlatAffineSectionBassTransition i).app R) _).2.2 x).mp hx

/-- Every actual seed-kernel class comes from the original shifted cone boundary. -/
theorem original_transition_boundary_surjects_kernel (i : ℕ) (R : CommRingCat.{u}) (d : ℤ)
    (x : stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram i).obj R) d)
    (hx : (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassTransition i).app R) x = 0) :
    ∃ y, boundedFlatAffineSectionBassMapConnecting i (i + 1) R R
      ((boundedFlatAffineSectionBassTransition i).app R) d y = x :=
  ((boundedFlatAffineSectionBassMap_longExactSequence i (i + 1) R R
    ((boundedFlatAffineSectionBassTransition i).app R) d).2.1 x).mp hx

/-- The genuine original coefficient square commutes with the actual signed seed boundary. -/
theorem original_transition_boundary_naturality (i : ℕ) {R S : CommRingCat.{u}}
    (f : R ⟶ S) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeMap (actualTransitionSquare i f)) ≫
      boundedFlatAffineSectionBassMapConnecting i (i + 1) S S
        ((boundedFlatAffineSectionBassTransition i).app S) d =
      boundedFlatAffineSectionBassMapConnecting i (i + 1) R R
        ((boundedFlatAffineSectionBassTransition i).app R) d ≫
          (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassDiagram i).map f) :=
  stableMappingConeConnecting_naturality (actualTransitionSquare i f)
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i (i + 1) R R _)
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i (i + 1) S S _) d

/-- Stable original coefficient sides preserve the actual iterated-seed cone map. -/
theorem original_transition_coneMap_isStableEquivalence (i : ℕ) {R S : CommRingCat.{u}}
    (f : R ⟶ S)
    (hi : IsStableEquivalence ((boundedFlatAffineSectionBassDiagram i).map f))
    (hj : IsStableEquivalence ((boundedFlatAffineSectionBassDiagram (i + 1)).map f)) :
    IsStableEquivalence (mappingConeMap (actualTransitionSquare i f)) :=
  boundedFlatAffineSectionBassMap_coneMap_isStableEquivalence i (i + 1) R R
    ((boundedFlatAffineSectionBassTransition i).app R) i (i + 1) S S
    ((boundedFlatAffineSectionBassTransition i).app S) (actualTransitionSquare i f) hi hj

end Quillen.Tests.SectionBassStableSequence
