/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeSelfMap

/-!
# The actual Bass telescope fixed-map consumers

These consumers retain the unchanged initial Laurent seed, all later original transitions,
independent cylinder and loop coordinates, genuine coefficient arrows and signed stable maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SectionBassTelescopeSelfMap

/-- The actual initial face of the stable map retains the single original Laurent seed. -/
theorem original_initial_seed (R : CommRingCat.{u}) (k : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space k) :
    (boundedFlatAffineSectionBassTelescopeBassMap.app R).map k
      (boundedFlatAffineSectionBassTelescopeInitial.app R |>.map k x) =
      ((KTheory.Bass.strictRingDiagramFunctor.map
        boundedFlatAffineSectionBassTelescopeInitial).app R).map k
          (boundedFlatAffineSectionBassSeed.app R |>.map k x) :=
  congrArg (fun m => m.map k x) (boundedFlatAffineSectionBassTelescopeBassMap_initial R)

/-- Original telescope height and internal loop time retain the same iterated seed map. -/
theorem original_cylinder_seed_loop (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space k) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassTelescopeBassMap.app R).map k
      (Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
        (fun i => (boundedFlatAffineSectionBassTransition i).app R) k i (s, x))) t =
      (Telescope.diagramConeIso boundedFlatAffineSectionBassDiagram
        boundedFlatAffineSectionBassTransition (laurentSquare R)).inv.map k
        (Telescope.cylinder
          (fun i => mappingCone (StrictSquare.comparison
            ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))))
          (Telescope.diagramConeTransition boundedFlatAffineSectionBassDiagram
            boundedFlatAffineSectionBassTransition (laurentSquare R)) k i
          (s, Path.toContinuousMap
            (((boundedFlatAffineSectionBassSuccessorIso i).hom.app R).map k
              ((boundedFlatAffineSectionBassTransition i).app R |>.map k x)) t)) := rfl

/-- The exact unchanged telescope-to-Bass map is bijective in every negative signed degree. -/
theorem original_negative_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((n + 1 : ℕ) : ℤ))).map
      (boundedFlatAffineSectionBassTelescopeBassMap.app R)) := by
  let := boundedFlatAffineSectionBassTelescopeBassMap_isStableEquivalence R
    (-((n + 1 : ℕ) : ℤ))
  exact ConcreteCategory.bijective_of_isIso _

/-- Actual shifted-stage inclusion is the inverse stable map of forward tail passage. -/
theorem original_tail_inverse (R : CommRingCat.{u}) (d : ℤ) :
    (stableHomotopyFunctor d).map
      (boundedFlatAffineSectionBassTelescopeToSuccessor.app R ≫
        Telescope.tailInclusion (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
          (fun i => (boundedFlatAffineSectionBassTransition i).app R)) =
      𝟙 (stableHomotopyGroup (boundedFlatAffineSectionBassTelescopeFunctor.obj R) d) :=
  Telescope.toTail_comp_tailInclusion_stableMap
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R) d

/-- Both original coefficient arrows commute with the exact telescope-to-Bass map. -/
theorem original_coefficient_composition {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionBassTelescopeFunctor.map f ≫
      boundedFlatAffineSectionBassTelescopeFunctor.map g ≫
      boundedFlatAffineSectionBassTelescopeBassMap.app T =
    boundedFlatAffineSectionBassTelescopeBassMap.app R ≫
      (KTheory.Bass.strictRingDiagramFunctor.obj
        boundedFlatAffineSectionBassTelescopeFunctor).map (f ≫ g) := by
  simpa only [Functor.map_comp, Category.assoc] using
    boundedFlatAffineSectionBassTelescopeBassMap.naturality (f ≫ g)

end Quillen.Tests.SectionBassTelescopeSelfMap
