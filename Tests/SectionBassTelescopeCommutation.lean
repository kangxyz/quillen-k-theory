/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeCommutation

/-!
# Actual Bass–telescope commutation consumers

The unchanged original successor tower, the single initial Laurent seed and its genuine Bass
image, original inclusions, arbitrary coefficients and signed degrees are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SectionBassTelescopeCommutation

/-- The original first seed image is transported to Bass of the single original seed. -/
theorem original_first_seed_transport (R : CommRingCat.{u}) (k : ℕ)
    (x : ((boundedFlatAffineSectionBassDiagram 1).obj R).space k) :
    ((boundedFlatAffineSectionBassSuccessorIso 1).hom.app R).map k
      ((boundedFlatAffineSectionBassTransition 1).app R |>.map k x) =
      ((KTheory.Bass.strictRingDiagramFunctor.map boundedFlatAffineSectionBassSeed).app R).map k
        (((boundedFlatAffineSectionBassSuccessorIso 0).hom.app R).map k x) :=
  congrArg (fun m => m.map k x)
    (NatTrans.congr_app (boundedFlatAffineSectionBassSuccessorIso_transition 0) R)

/-- The full comparison keeps original telescope height and loop time separate. -/
theorem original_cylinder_two_times (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).space k) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R).map k
      (Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
        (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R) k i (s, x))) t =
      (Telescope.diagramConeIso boundedFlatAffineSectionBassDiagram
        boundedFlatAffineSectionBassTransition (laurentSquare R)).inv.map k
        (Telescope.cylinder
          (fun i => mappingCone (StrictSquare.comparison
            ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))))
          (Telescope.diagramConeTransition boundedFlatAffineSectionBassDiagram
            boundedFlatAffineSectionBassTransition (laurentSquare R)) k i
          (s, Path.toContinuousMap
            (((boundedFlatAffineSectionBassSuccessorIso i).hom.app R).map k x) t)) := rfl

/-- At height one the actual comparison still glues through the unchanged original next seed. -/
theorem original_successor_seed_gluing (R : CommRingCat.{u}) (k i : ℕ)
    (x : ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).space k) :
    (boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R).map k
      (Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
        (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R) k i (1, x)) =
      (boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R).map k
        (Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
          (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R) k (i + 1)
          (0, (boundedFlatAffineSectionBassTransition (i + 1)).app R |>.map k x)) :=
  congrArg ((boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R).map k)
    (Telescope.cylinder_one (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
      (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R) k i x)

/-- Every original negative signed group sees a bijection under this exact original map. -/
theorem original_negative_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-((n + 1 : ℕ) : ℤ))).map
      (boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R)) := by
  let := boundedFlatAffineSectionBassSuccessorTelescopeComparison_isStableEquivalence R
    (-((n + 1 : ℕ) : ℤ))
  exact ConcreteCategory.bijective_of_isIso _

/-- Two original coefficient arrows commute with the same actual successor comparison. -/
theorem original_coefficient_composition {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionBassSuccessorTelescopeFunctor.map f ≫
      boundedFlatAffineSectionBassSuccessorTelescopeFunctor.map g ≫
      boundedFlatAffineSectionBassSuccessorTelescopeComparison.app T =
    boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R ≫
      (KTheory.Bass.strictRingDiagramFunctor.obj
        boundedFlatAffineSectionBassTelescopeFunctor).map (f ≫ g) := by
  simpa only [Functor.map_comp, Category.assoc] using
    boundedFlatAffineSectionBassSuccessorTelescopeComparison.naturality (f ≫ g)

/-- The first actual successor face retains Bass of the original initial section inclusion. -/
theorem original_initial_inclusion (R : CommRingCat.{u}) :
    (Telescope.diagramInclusion (fun i => boundedFlatAffineSectionBassDiagram (i + 1))
        (fun i => boundedFlatAffineSectionBassTransition (i + 1)) 0).app R ≫
        boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R =
      (boundedFlatAffineSectionBassSuccessorIso 0).hom.app R ≫
        (KTheory.Bass.strictRingDiagramFunctor.map
          boundedFlatAffineSectionBassTelescopeInitial).app R :=
  boundedFlatAffineSectionBassSuccessorTelescopeComparison_inclusion 0 R

end Quillen.Tests.SectionBassTelescopeCommutation
