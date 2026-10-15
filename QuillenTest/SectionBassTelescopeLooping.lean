/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeLooping

/-!
# Original Bass telescope-loop consumers

These consumers retain the original Laurent seed face, arbitrary coefficient maps, literal
independent cylinder and loop times, original signed stable inclusions and negative degrees.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassTelescopeLooping

open Quillen

/-- The height-one initial cylinder glues through the unchanged original Laurent seed. -/
theorem original_seed_gluing (R : CommRingCat.{u}) (k : ℕ) (t : unitInterval)
    (x : Path ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point k)
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point k)) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassTelescopeLoopComparison.app R).map k
      (Telescope.cylinder
        (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
        (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) k 0
        (1, x))) t =
      Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
        (fun i => (boundedFlatAffineSectionBassTransition i).app R) k 1
        (0, (boundedFlatAffineSectionBassSeed.app R).map k (x t)) := by
  rw [boundedFlatAffineSectionBassTelescopeLoopComparison_cylinder, Telescope.cylinder_one]
  rfl

/-- Coefficients act at each original stage without moving cylinder height or loop time. -/
theorem original_coefficient_two_times {R S : CommRingCat.{u}} (f : R ⟶ S)
    (k i : ℕ) (s t : unitInterval)
    (x : Path (((boundedFlatAffineSectionBassDiagram i).obj R).point k)
      (((boundedFlatAffineSectionBassDiagram i).obj R).point k)) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassTelescopeLoopComparison.app S).map k
      ((boundedFlatAffineSectionBassLoopTelescopeFunctor.map f).map k
        (Telescope.cylinder
          (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
          (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) k i
          (s, x)))) t =
      Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram i).obj S)
        (fun i => (boundedFlatAffineSectionBassTransition i).app S) k i
        (s, ((boundedFlatAffineSectionBassDiagram i).map f).map k (x t)) := rfl

/-- Every actual negative stable class has a unique original looped-telescope preimage. -/
theorem original_negative_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((n + 1 : ℕ) : ℤ))).map
      (boundedFlatAffineSectionBassTelescopeLoopComparison.app R)) := by
  let := boundedFlatAffineSectionBassTelescopeLoopComparison_isStableEquivalence R
    (-((n + 1 : ℕ) : ℤ))
  exact ConcreteCategory.bijective_of_isIso _

/-- The unchanged original stage inclusion keeps the actual signed loop shift. -/
theorem original_signed_inclusion (R : CommRingCat.{u}) (d : ℤ) (i : ℕ) :
    (stableHomotopyFunctor d).map (Telescope.inclusion
        (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
        (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) i) ≫
      (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeLoopComparison.app R) ≫
      (parameterStableHomotopyIso (boundedFlatAffineSectionBassTelescope R) d).hom =
    (parameterStableHomotopyIso ((boundedFlatAffineSectionBassDiagram i).obj R) d).hom ≫
      (stableHomotopyFunctor (d + 1)).map
        ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) := by
  rw [← Category.assoc, ← Functor.map_comp,
    boundedFlatAffineSectionBassTelescopeLoopComparison_inclusion]
  exact parameterStableHomotopyIso_naturality
    ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) d

/-- At level zero, the actual initial face is still the loop of the original initial inclusion. -/
theorem original_initial_zero_level (R : CommRingCat.{u}) (t : unitInterval)
    (x : Path ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point 0)
      ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point 0)) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassTelescopeLoopComparison.app R).map 0
      ((Telescope.inclusion
        (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
        (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) 0).map 0
        x)) t = (boundedFlatAffineSectionBassTelescopeInitial.app R).map 0 (x t) := rfl

end QuillenTest.SectionBassTelescopeLooping
