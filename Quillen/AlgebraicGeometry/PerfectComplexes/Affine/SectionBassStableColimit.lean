/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.Topology.Prespectrum.TelescopeStableColimit

/-!
# The actual signed stable groups of the section Bass telescope

The original stable groups of the actual iterated Bass stages, with the iterated original
Laurent seed as connecting arrows, have a canonical colimit isomorphism onto the unchanged
stable group of the actual telescope. The comparison holds in every integer degree and is
natural for the original strict coefficient maps. All point-set hypotheses are discharged.

This does not identify these stage groups with classical Bass groups or assert a
nonconnective Thomason–Trobaugh localization theorem.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Actual stable groups of the original Bass stages and their unchanged connecting arrows. -/
def boundedFlatAffineSectionBassStableDiagram (R : CommRingCat.{u}) (d : ℤ) :
    ℕ ⥤ AddCommGrpCat.{u+1} :=
  Telescope.stageStableDiagram (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R) d

/-- The original strict coefficient map on the actual stage stable groups. -/
def boundedFlatAffineSectionBassStableDiagramMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    (d : ℤ) : boundedFlatAffineSectionBassStableDiagram R d ⟶
      boundedFlatAffineSectionBassStableDiagram S d :=
  Telescope.stageStableDiagramMap
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) d

/-- Coefficients act strictly on the entire actual stage stable diagram. -/
def boundedFlatAffineSectionBassStableDiagramFunctor (d : ℤ) :
    CommRingCat.{u} ⥤ (ℕ ⥤ AddCommGrpCat.{u+1}) where
  obj R := boundedFlatAffineSectionBassStableDiagram R d
  map f := boundedFlatAffineSectionBassStableDiagramMap f d
  map_id R := by
    apply NatTrans.ext
    funext i
    exact (congrArg ((stableHomotopyFunctor d).map)
      ((boundedFlatAffineSectionBassDiagram i).map_id R)).trans
      ((stableHomotopyFunctor d).map_id _)
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact (congrArg ((stableHomotopyFunctor d).map)
      ((boundedFlatAffineSectionBassDiagram i).map_comp f g)).trans
      ((stableHomotopyFunctor d).map_comp _ _)

/-- The filtered colimit of the unchanged stage groups, with the original coefficient maps. -/
def boundedFlatAffineSectionBassStableColimitFunctor (d : ℤ) :
    CommRingCat.{u} ⥤ AddCommGrpCat.{u+1} :=
  boundedFlatAffineSectionBassStableDiagramFunctor d ⋙ colim

/-- The canonical comparison is an isomorphism in every signed degree, unconditionally. -/
def boundedFlatAffineSectionBassStableColimitIso (R : CommRingCat.{u}) (d : ℤ) :
    colimit (boundedFlatAffineSectionBassStableDiagram R d) ≅
      stableHomotopyGroup (boundedFlatAffineSectionBassTelescope R) d :=
  Telescope.stableColimitIso (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R) d

/-- Each canonical stage leg maps to exactly the original telescope stage inclusion. -/
@[reassoc] theorem boundedFlatAffineSectionBassStableColimitIso_ι_hom
    (R : CommRingCat.{u}) (d : ℤ) (i : ℕ) :
    colimit.ι (boundedFlatAffineSectionBassStableDiagram R d) i ≫
        (boundedFlatAffineSectionBassStableColimitIso R d).hom =
      (stableHomotopyFunctor d).map ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) :=
  Telescope.stableColimitIso_ι_hom
    (fun j ↦ (boundedFlatAffineSectionBassDiagram j).obj R)
    (fun j ↦ (boundedFlatAffineSectionBassTransition j).app R) d i

/-- The actual comparison commutes with every original strict coefficient map. -/
@[reassoc] theorem boundedFlatAffineSectionBassStableColimitIso_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ) :
    colimMap (boundedFlatAffineSectionBassStableDiagramMap f d) ≫
        (boundedFlatAffineSectionBassStableColimitIso S d).hom =
      (boundedFlatAffineSectionBassStableColimitIso R d).hom ≫
        (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f) :=
  Telescope.stableColimitIso_naturality
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj S)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app S)
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).map f)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).naturality f) d

/-- The signed colimit comparison is a natural isomorphism of the actual coefficient functors. -/
def boundedFlatAffineSectionBassStableColimitNatIso (d : ℤ) :
    boundedFlatAffineSectionBassStableColimitFunctor d ≅
      boundedFlatAffineSectionBassTelescopeFunctor ⋙ stableHomotopyFunctor d :=
  NatIso.ofComponents (fun R ↦ boundedFlatAffineSectionBassStableColimitIso R d)
    (fun f ↦ boundedFlatAffineSectionBassStableColimitIso_naturality f d)

/-- Every component is exactly the original canonical telescope comparison. -/
@[simp] theorem boundedFlatAffineSectionBassStableColimitNatIso_hom_app
    (d : ℤ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassStableColimitNatIso d).hom.app R =
      (boundedFlatAffineSectionBassStableColimitIso R d).hom := rfl

end Quillen.PerfectComplexes
