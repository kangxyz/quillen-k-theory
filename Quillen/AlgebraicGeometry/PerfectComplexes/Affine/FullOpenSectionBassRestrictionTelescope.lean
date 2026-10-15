/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassRestrictionTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassTelescope
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap

/-!
# The original coarse-to-full section restriction on the Bass telescopes

The proved original restriction seed square makes the unchanged finite arrows compatible
with the actual transitions. Their literal reduced telescope map retains every original
stage inclusion and cylinder height. No compactness or stability premise is used to construct it.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The unchanged finite restriction arrows induce the actual coefficient-natural telescope map. -/
def boundedFlatAffineSectionFullOpenBassTelescopeRestriction :
    boundedFlatAffineSectionOpenBassTelescopeFunctor j ⟶
      boundedFlatAffineFullOpenSectionBassTelescopeFunctor j :=
  Telescope.diagramMap (boundedFlatAffineSectionOpenBassDiagram j)
    (boundedFlatAffineFullOpenSectionBassDiagram j)
    (boundedFlatAffineSectionOpenBassTransition j)
    (boundedFlatAffineFullOpenSectionBassTransition j)
    (boundedFlatAffineSectionFullOpenBassRestriction j)
    (boundedFlatAffineSectionFullOpenBassRestriction_transition j)

/-- Every original finite restriction retains its cylinder coordinate and level. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeRestriction_cylinder
    (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenBassDiagram j i).obj a).space n) :
    ((boundedFlatAffineSectionFullOpenBassTelescopeRestriction j).app a).map n
        (Telescope.cylinder
          (fun k ↦ (boundedFlatAffineSectionOpenBassDiagram j k).obj a)
          (fun k ↦ (boundedFlatAffineSectionOpenBassTransition j k).app a) n i (t, x)) =
      Telescope.cylinder (fun k ↦ (boundedFlatAffineFullOpenSectionBassDiagram j k).obj a)
        (fun k ↦ (boundedFlatAffineFullOpenSectionBassTransition j k).app a) n i
          (t, ((boundedFlatAffineSectionFullOpenBassRestriction j i).app a).map n x) := rfl

/-- Every original stage inclusion retains the same finite restriction face. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeInclusion_restriction (i : ℕ) :
    boundedFlatAffineSectionOpenBassTelescopeInclusion j i ≫
        boundedFlatAffineSectionFullOpenBassTelescopeRestriction j =
      boundedFlatAffineSectionFullOpenBassRestriction j i ≫
        boundedFlatAffineFullOpenSectionBassTelescopeInclusion j i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The initial telescope faces preserve precisely the original restriction transformation. -/
theorem boundedFlatAffineSectionFullOpenBassTelescopeInitial_restriction :
    boundedFlatAffineSectionOpenBassTelescopeInitial j ≫
        boundedFlatAffineSectionFullOpenBassTelescopeRestriction j =
      boundedFlatAffineSectionFullOpenPrespectrumTransformation j ≫
        boundedFlatAffineFullOpenSectionBassTelescopeInitial j :=
  boundedFlatAffineSectionFullOpenBassTelescopeInclusion_restriction j 0

end Quillen.PerfectComplexes
