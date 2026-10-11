/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeCommutation
public import Quillen.Topology.Prespectrum.TelescopeTail

/-!
# The original Bass telescope maps stably to its own Bass image

Actual forward tail passage uses the same original iterated seed on each cylinder. Composing
it with the genuine successor comparison gives a coefficient-natural stable map from the
unchanged telescope to its actual Bass image, retaining the original initial Laurent seed.
This does not identify fixed-degree classical groups or assert stability of any finite seed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Actual forward tail passage uses the original iterated Laurent seed at the same height. -/
def boundedFlatAffineSectionBassTelescopeToSuccessor :
    boundedFlatAffineSectionBassTelescopeFunctor.{u} ⟶
      boundedFlatAffineSectionBassSuccessorTelescopeFunctor where
  app R := Telescope.toTail (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R)
  naturality R S f := Telescope.toTail_naturality
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R)
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i => (boundedFlatAffineSectionBassTransition i).app S)
    (fun i => (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i => (boundedFlatAffineSectionBassTransition i).naturality f)

/-- The original stages discharge T1 for the actual forward tail map. -/
theorem boundedFlatAffineSectionBassTelescopeToSuccessor_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassTelescopeToSuccessor.app R) :=
  Telescope.toTail_isStableEquivalence
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R)

/-- The unchanged original Bass telescope maps to its actual Bass image. -/
def boundedFlatAffineSectionBassTelescopeBassMap :
    boundedFlatAffineSectionBassTelescopeFunctor.{u} ⟶
      KTheory.Bass.strictRingDiagramFunctor.obj boundedFlatAffineSectionBassTelescopeFunctor :=
  boundedFlatAffineSectionBassTelescopeToSuccessor ≫
    boundedFlatAffineSectionBassSuccessorTelescopeComparison

/-- This exact original map is stable in every signed degree, with no finite-seed premise. -/
theorem boundedFlatAffineSectionBassTelescopeBassMap_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassTelescopeBassMap.app R) :=
  (boundedFlatAffineSectionBassTelescopeToSuccessor_isStableEquivalence R).comp
    (boundedFlatAffineSectionBassSuccessorTelescopeComparison_isStableEquivalence R)

/-- The literal original stage face passes through the same original stage transition. -/
theorem boundedFlatAffineSectionBassTelescopeToSuccessor_inclusion
    (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassTelescopeInclusion i).app R ≫
        boundedFlatAffineSectionBassTelescopeToSuccessor.app R =
      (boundedFlatAffineSectionBassTransition i).app R ≫
        (Telescope.diagramInclusion (fun i => boundedFlatAffineSectionBassDiagram (i + 1))
          (fun i => boundedFlatAffineSectionBassTransition (i + 1)) i).app R :=
  Telescope.inclusion_toTail (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R) i

/-- Every original stage retains its true seed image and the actual Bass image of its inclusion. -/
theorem boundedFlatAffineSectionBassTelescopeBassMap_inclusion (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassTelescopeInclusion i).app R ≫
        boundedFlatAffineSectionBassTelescopeBassMap.app R =
      (boundedFlatAffineSectionBassTransition i).app R ≫
        (boundedFlatAffineSectionBassSuccessorIso i).hom.app R ≫
        (KTheory.Bass.strictRingDiagramFunctor.map
          (boundedFlatAffineSectionBassTelescopeInclusion i)).app R := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R)
      (boundedFlatAffineSectionBassTelescopeToSuccessor_inclusion i R)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((boundedFlatAffineSectionBassTransition i).app R ≫ ·)
          (boundedFlatAffineSectionBassSuccessorTelescopeComparison_inclusion i R))))

/-- At the original initial face, this map is exactly the original Laurent seed followed by
Bass of the unchanged initial inclusion. -/
theorem boundedFlatAffineSectionBassTelescopeBassMap_initial (R : CommRingCat.{u}) :
    boundedFlatAffineSectionBassTelescopeInitial.app R ≫
        boundedFlatAffineSectionBassTelescopeBassMap.app R =
      boundedFlatAffineSectionBassSeed.app R ≫
        (KTheory.Bass.strictRingDiagramFunctor.map
          boundedFlatAffineSectionBassTelescopeInitial).app R :=
  (boundedFlatAffineSectionBassTelescopeBassMap_inclusion 0 R).trans
    (by
      change _ ≫ (𝟙 _ ≫ _) = _
      rw [Category.id_comp]
      rfl)

end Quillen.PerfectComplexes
