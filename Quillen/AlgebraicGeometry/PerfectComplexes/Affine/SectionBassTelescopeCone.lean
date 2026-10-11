/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.Topology.Prespectrum.TelescopeConeStableColimit

/-!
# The actual coefficient-map cone of the section Bass telescope

The unchanged telescope coefficient map has its original cone strictly identified with the
original telescope of finite-stage coefficient cones. Genuine T1 at every actual Bass stage
then gives the canonical signed cone-group colimit isomorphism, retaining each original stage
cone map. No connectivity of the full telescope is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The actual transitions of the finite-stage coefficient cones use the original iterated seed.
-/
def boundedFlatAffineSectionBassConeTransition (i : ℕ) :
    mappingCone ((boundedFlatAffineSectionBassDiagram i).map f) ⟶
      mappingCone ((boundedFlatAffineSectionBassDiagram (i + 1)).map f) :=
  Telescope.coneTransition
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) i

/-- The original finite-stage cone map uses the unchanged two telescope inclusions. -/
def boundedFlatAffineSectionBassConeStageMap (i : ℕ) :
    mappingCone ((boundedFlatAffineSectionBassDiagram i).map f) ⟶
      mappingCone (boundedFlatAffineSectionBassTelescopeMap f) :=
  Telescope.coneStageMap
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) i

/-- The unchanged coefficient-map cone is strictly the actual telescope of coefficient cones.
-/
def boundedFlatAffineSectionBassTelescopeConeIso :
    mappingCone (boundedFlatAffineSectionBassTelescopeMap f) ≅
      Telescope.prespectrum (fun i ↦ mappingCone ((boundedFlatAffineSectionBassDiagram i).map f))
        (boundedFlatAffineSectionBassConeTransition f) :=
  Telescope.coneIso
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f)

/-- Actual signed cone groups are canonically the colimit of original finite-stage cone groups.
-/
def boundedFlatAffineSectionBassTelescopeConeStableColimitIso (d : ℤ) :
    colimit (Telescope.stageStableDiagram
      (fun i ↦ mappingCone ((boundedFlatAffineSectionBassDiagram i).map f))
      (boundedFlatAffineSectionBassConeTransition f) d) ≅
        stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) d :=
  Telescope.coneStableColimitIso
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) d

/-- Each original cone inclusion is the canonical stage map on the actual signed colimit. -/
@[reassoc] theorem boundedFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom
    (d : ℤ) (i : ℕ) :
    colimit.ι (Telescope.stageStableDiagram
        (fun i ↦ mappingCone ((boundedFlatAffineSectionBassDiagram i).map f))
        (boundedFlatAffineSectionBassConeTransition f) d) i ≫
      (boundedFlatAffineSectionBassTelescopeConeStableColimitIso f d).hom =
        (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassConeStageMap f i) :=
  Telescope.coneStableColimitIso_ι_hom
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) d i

/-- Every actual signed telescope-cone class is represented by an unchanged finite-stage cone.
-/
theorem boundedFlatAffineSectionBassTelescopeCone_exists_stable_representative (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) d) :
    ∃ i : ℕ, ∃ z : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSectionBassDiagram i).map f)) d,
      (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassConeStageMap f i) z = x := by
  let e := boundedFlatAffineSectionBassTelescopeConeStableColimitIso f d
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨i, z, hz⟩ := Concrete.colimit_exists_rep
    (Telescope.stageStableDiagram
      (fun i ↦ mappingCone ((boundedFlatAffineSectionBassDiagram i).map f))
      (boundedFlatAffineSectionBassConeTransition f) d) (e.inv x)
  refine ⟨i, z, ?_⟩
  have hstage := ConcreteCategory.congr_hom
    (boundedFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom f d i) z
  have hx := ConcreteCategory.congr_hom e.inv_hom_id x
  exact hstage.symm.trans ((congrArg e.hom hz).trans hx)

end Quillen.PerfectComplexes
