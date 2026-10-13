/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConeExcision
public import Quillen.Topology.Prespectrum.ConeHomotopySquareStableExcision
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Stable original whole-track cone comparisons between finite Bass stages

Actual all-stage cone excision discharges every intermediate row of the original full-track
factorization. Thus supplied whole homotopy squares with original stable side maps induce
stable equivalences on their unchanged cones and parameter-correct loops. No positive-level
weak equivalence, Omega structure, low-level connectivity or strictification is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (i j i' j' : ℕ) (R S R' S' : CommRingCat.{u})
  (f : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram j).obj S)
  (g : (boundedFlatAffineSectionBassDiagram i').obj R' ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (a : (boundedFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedFlatAffineSectionBassDiagram i').obj R')
  (b : (boundedFlatAffineSectionBassDiagram j).obj S ⟶
    (boundedFlatAffineSectionBassDiagram j').obj S')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- Stable sides preserve the unchanged supplied-track cone map at arbitrary finite stages. -/
theorem boundedFlatAffineSectionBass_wholeTrackCone_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) :
    IsStableEquivalence (mappingConeSquareMap f g a b H) :=
  mappingConeSquareMap_isStableEquivalence_of_excision f g a b H
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j R S f)
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j' R S' (f ≫ b))
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i j' R S' (a ≫ g))
    (boundedFlatAffineSectionBass_map_coneFiber_isStableEquivalence i' j' R' S' g) ha hb

/-- Parameter looping preserves the same full-track cone comparison in all signed degrees. -/
theorem boundedFlatAffineSectionBass_loopedWholeTrackCone_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) :
    IsStableEquivalence (parameterLoopingMap (mappingConeSquareMap f g a b H)) :=
  parameterLoopingMap_isStableEquivalence _
    (boundedFlatAffineSectionBass_wholeTrackCone_isStableEquivalence
      i j i' j' R S R' S' f g a b H ha hb)

end Quillen.PerfectComplexes
