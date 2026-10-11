/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision
public import Quillen.Topology.Prespectrum.ConeStableNaturality

/-!
# Original stable cone sequences throughout the actual finite Bass iteration

The genuine all-stage cone comparison supplies the signed boundary and all three recurring
exactness positions for every original arrow between actual finite Bass stages. Strict squares
with stable original sides preserve their unchanged cones. All growth, point HEP and excision
premises are discharged; the construction keeps the original signed groups and maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j : ℕ) (R S : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)

/-- The actual signed original cone boundary for an unchanged arrow between finite Bass stages. -/
def boundedFlatAffineSectionBassMapConnecting (d : ℤ) :
    stableHomotopyGroup (mappingCone f) (d + 1) ⟶
      stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram i).obj R) d :=
  stableMappingConeConnecting f
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f) d

/-- Original finite Bass-stage arrows have the full signed stable cone sequence unconditionally. -/
theorem boundedFlatAffineSectionBassMap_longExactSequence (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (boundedFlatAffineSectionBassMapConnecting i j R S f d) ∧
    Function.Exact (boundedFlatAffineSectionBassMapConnecting i j R S f d)
      ((stableHomotopyFunctor d).map f) ∧
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  stableMappingConeLongExactSequence f
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f) d

/-- Original stable sides of a square between finite Bass-stage arrows preserve the actual cones. -/
theorem boundedFlatAffineSectionBassMap_coneMap_isStableEquivalence
    (i' j' : ℕ) (R' S' : CommRingCat.{u})
    (g : (boundedFlatAffineSectionBassDiagram i').obj R' ⟶
      (boundedFlatAffineSectionBassDiagram j').obj S')
    (sq : Arrow.mk f ⟶ Arrow.mk g)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_excision sq
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f)
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i' j' R' S' g) hl hr

end Quillen.PerfectComplexes
