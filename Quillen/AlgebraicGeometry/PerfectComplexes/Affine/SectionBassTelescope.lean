/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTransition
public import Quillen.Topology.Prespectrum.TelescopeDiagram

/-!
# The actual original section Bass telescope

The original proved Laurent seed and all its Bass images form the actual reduced telescope.
Coefficient maps act on every original cylinder, strictly functorially. The initial inclusion
is the original stage-zero face. This construction makes no identification with classical Bass
groups and does not assert a nonconnective Thomason–Trobaugh theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original reduced telescope of the proved geometric Bass tower, as a strict ring diagram. -/
def boundedFlatAffineSectionBassTelescopeFunctor : CommRingCat.{u} ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor boundedFlatAffineSectionBassDiagram
    boundedFlatAffineSectionBassTransition

/-- The actual quotient telescope, retaining the same original iterated seed at every stage. -/
def boundedFlatAffineSectionBassTelescope (R : CommRingCat.{u}) : LoopPrespectrum.{u+1} :=
  boundedFlatAffineSectionBassTelescopeFunctor.obj R

/-- The original coefficient map on the constructed Bass telescope. -/
def boundedFlatAffineSectionBassTelescopeMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionBassTelescope R ⟶ boundedFlatAffineSectionBassTelescope S :=
  boundedFlatAffineSectionBassTelescopeFunctor.map f

/-- Every actual Bass stage includes through the original initial face of its cylinder. -/
def boundedFlatAffineSectionBassTelescopeInclusion (i : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassTelescopeFunctor :=
  Telescope.diagramInclusion _ _ i

/-- The original geometric section prespectrum enters at the unchanged stage-zero face. -/
def boundedFlatAffineSectionBassTelescopeInitial :
    boundedFlatAffineSectionPrespectrumFunctor.{u} ⟶ boundedFlatAffineSectionBassTelescopeFunctor :=
  boundedFlatAffineSectionBassTelescopeInclusion 0

/-- Identity coefficients induce the literal identity on the actual quotient telescope. -/
theorem boundedFlatAffineSectionBassTelescopeMap_id (R : CommRingCat.{u}) :
    boundedFlatAffineSectionBassTelescopeMap (𝟙 R) = 𝟙 (boundedFlatAffineSectionBassTelescope R) :=
  boundedFlatAffineSectionBassTelescopeFunctor.map_id R

/-- Composing coefficients gives the literal composite telescope map. -/
theorem boundedFlatAffineSectionBassTelescopeMap_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionBassTelescopeMap (f ≫ g) =
      boundedFlatAffineSectionBassTelescopeMap f ≫ boundedFlatAffineSectionBassTelescopeMap g :=
  boundedFlatAffineSectionBassTelescopeFunctor.map_comp f g

/-- The original cylinder coordinate and every actual iterated coefficient map are retained. -/
theorem boundedFlatAffineSectionBassTelescopeMap_cylinder {R S : CommRingCat.{u}}
    (f : R ⟶ S) (k i : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space k) :
    (boundedFlatAffineSectionBassTelescopeMap f).map k
        (Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
          (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k i (s, x)) =
      Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj S)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app S) k i
          (s, ((boundedFlatAffineSectionBassDiagram i).map f).map k x) := rfl

/-- The initial natural map retains the literal initial face in every original level. -/
theorem boundedFlatAffineSectionBassTelescopeInitial_apply (R : CommRingCat.{u}) (k : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space k) :
    (boundedFlatAffineSectionBassTelescopeInitial.app R).map k x =
      Telescope.cylinder (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
        (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) k 0 (0, x) := rfl

/-- Every original telescope cylinder joins consecutive inclusions through the same Bass seed.
-/
def boundedFlatAffineSectionBassTelescopeInclusionHomotopy (R : CommRingCat.{u}) (i : ℕ) :
    Homotopy ((boundedFlatAffineSectionBassTelescopeInclusion i).app R)
      ((boundedFlatAffineSectionBassTransition i).app R ≫
        (boundedFlatAffineSectionBassTelescopeInclusion (i + 1)).app R) :=
  Telescope.diagramInclusionHomotopy _ _ R i

end Quillen.PerfectComplexes
