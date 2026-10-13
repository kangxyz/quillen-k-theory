/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope

/-! The original initial inclusion, actual seed gluing and full telescope coefficient cylinders. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassTelescope

open Quillen

/-- The first original telescope cylinder joins the initial inclusion to the proved actual seed. -/
def originalSeedInclusionHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedFlatAffineSectionBassTelescopeInitial.app R)
      (boundedFlatAffineSectionBassSeed.app R ≫
        (boundedFlatAffineSectionBassTelescopeInclusion 1).app R) :=
  boundedFlatAffineSectionBassTelescopeInclusionHomotopy R 0

/-- The original top of stage zero is glued using exactly the previously proved Laurent seed. -/
theorem original_seed_gluing (R : CommRingCat.{u}) (k : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space k) :
    Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k 0 (1, x) =
      ((boundedFlatAffineSectionBassTelescopeInclusion 1).app R).map k
        ((boundedFlatAffineSectionBassSeed.app R).map k x) :=
  Telescope.cylinder_one (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
    (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k 0 x

/-- The original initial inclusion commutes with two independent coefficient maps. -/
theorem initial_two_coefficient_square {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedFlatAffineSectionBassTelescopeInitial.app T =
      boundedFlatAffineSectionBassTelescopeInitial.app R ≫
        boundedFlatAffineSectionBassTelescopeMap f ≫
        boundedFlatAffineSectionBassTelescopeMap g := by
  calc
    _ = boundedFlatAffineSectionBassTelescopeInitial.app R ≫
        boundedFlatAffineSectionBassTelescopeMap (f ≫ g) :=
      boundedFlatAffineSectionBassTelescopeInitial.naturality (f ≫ g)
    _ = _ := by rw [boundedFlatAffineSectionBassTelescopeMap_comp]; rfl

/-- Two coefficient changes retain the actual stage, cylinder time and composed original map. -/
theorem two_coefficient_cylinder {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedFlatAffineSectionBassTelescopeMap g).map k
        ((boundedFlatAffineSectionBassTelescopeMap f).map k
          (Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
            (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k i (s, x))) =
      Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj T)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app T) k i
          (s, ((boundedFlatAffineSectionBassDiagram i).map (f ≫ g)).map k x) := by
  rw [boundedFlatAffineSectionBassTelescopeMap_cylinder,
    boundedFlatAffineSectionBassTelescopeMap_cylinder, Functor.map_comp]
  rfl

/-- Original telescope time and original structure time remain independent. -/
theorem independent_telescope_parameters (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedFlatAffineSectionBassTelescope R).structureMap k
        (Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
          (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k i (s, x)) t =
      Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) (k + 1) i
          (s, ((boundedFlatAffineSectionBassDiagram i).obj R).structureMap k x t) := rfl

/-- The same actual point is retained along every stage's entire collapsed base line. -/
theorem original_collapsed_base_line (R : CommRingCat.{u}) (k i : ℕ) (s : unitInterval) :
    Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k i
          (s, ((boundedFlatAffineSectionBassDiagram i).obj R).point k) =
      (boundedFlatAffineSectionBassTelescope R).point k :=
  Telescope.cylinder_point _ _ k i s

end QuillenTest.SectionBassTelescope
