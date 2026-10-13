/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.Topology.Prespectrum.TelescopeParameterLoopingStable

/-!
# Looping the actual original section Bass telescope

The original iterated Laurent seed is looped at every stage. The unchanged cylinder comparison
from its actual telescope to the loop of the original Bass telescope is coefficient-natural and
stable. All stage separation hypotheses are discharged by the proved original model topology.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual telescope of looped original Bass stages and looped original seed images. -/
def boundedFlatAffineSectionBassLoopTelescopeFunctor :
    CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1} :=
  Telescope.diagramFunctor
    (fun i => boundedFlatAffineSectionBassDiagram i ⋙ parameterLoopingFunctor)
    (fun i => Functor.whiskerRight (boundedFlatAffineSectionBassTransition i)
      parameterLoopingFunctor)

/-- The genuine cylinder comparison, naturally in every original coefficient ring. -/
def boundedFlatAffineSectionBassTelescopeLoopComparison :
    boundedFlatAffineSectionBassLoopTelescopeFunctor.{u} ⟶
      boundedFlatAffineSectionBassTelescopeFunctor ⋙ parameterLoopingFunctor where
  app R := Telescope.parameterLoopingComparison
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R)
  naturality R S f :=
    Telescope.parameterLoopingComparison_naturality
      (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
      (fun i => (boundedFlatAffineSectionBassTransition i).app R)
      (fun i => (boundedFlatAffineSectionBassDiagram i).obj S)
      (fun i => (boundedFlatAffineSectionBassTransition i).app S)
      (fun i => (boundedFlatAffineSectionBassDiagram i).map f)
      (fun i => (boundedFlatAffineSectionBassTransition i).naturality f)

/-- Every concrete topology premise is discharged for the original iterated-seed tower. -/
theorem boundedFlatAffineSectionBassTelescopeLoopComparison_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassTelescopeLoopComparison.app R) :=
  Telescope.parameterLoopingComparison_isStableEquivalence
    (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition i).app R)

/-- The original Bass cylinder height and loop time are unchanged at every actual stage. -/
theorem boundedFlatAffineSectionBassTelescopeLoopComparison_cylinder
    (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : Path (((boundedFlatAffineSectionBassDiagram i).obj R).point k)
      (((boundedFlatAffineSectionBassDiagram i).obj R).point k)) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassTelescopeLoopComparison.app R).map k
      (Telescope.cylinder
        (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
        (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) k i
        (s, x))) t =
      Telescope.cylinder (fun i => (boundedFlatAffineSectionBassDiagram i).obj R)
        (fun i => (boundedFlatAffineSectionBassTransition i).app R) k i (s, x t) := rfl

/-- The exact stage face becomes the actual loop of the unchanged Bass-stage inclusion. -/
theorem boundedFlatAffineSectionBassTelescopeLoopComparison_inclusion
    (R : CommRingCat.{u}) (i : ℕ) :
    Telescope.inclusion
        (fun i => parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R))
        (fun i => parameterLoopingMap ((boundedFlatAffineSectionBassTransition i).app R)) i ≫
        boundedFlatAffineSectionBassTelescopeLoopComparison.app R =
      parameterLoopingMap ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) :=
  Telescope.inclusion_parameterLoopingComparison _ _ i

end Quillen.PerfectComplexes
