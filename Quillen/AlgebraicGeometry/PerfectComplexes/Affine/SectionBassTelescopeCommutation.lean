/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTopology
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSuccessor
public import Quillen.KTheory.Bass.StrictDiagramTelescope
public import Quillen.KTheory.Bass.StrictDiagramSuccessor

/-!
# The actual Bass image of the original Bass telescope

The telescope of the genuine Bass images maps coefficient-naturally and stably to Bass of
the original telescope. The same right-iteration identity transports every original iterated
seed to its Bass image, giving a comparison from the unchanged successor-stage telescope.
All topology hypotheses are discharged for the actual original section model and its iterates.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes

/-- The telescope of Bass applied to the original stages and the same iterated seed arrows. -/
def boundedFlatAffineSectionBassTransformedTelescopeFunctor :
    CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1} :=
  Telescope.diagramFunctor
    (fun i => KTheory.Bass.strictRingDiagramFunctor.obj (boundedFlatAffineSectionBassDiagram i))
    (fun i => KTheory.Bass.strictRingDiagramFunctor.map (boundedFlatAffineSectionBassTransition i))

/-- The genuine Bass–telescope comparison is natural in the original coefficient maps. -/
def boundedFlatAffineSectionBassTelescopeComparison :
    boundedFlatAffineSectionBassTransformedTelescopeFunctor.{u} ⟶
      KTheory.Bass.strictRingDiagramFunctor.obj boundedFlatAffineSectionBassTelescopeFunctor :=
  KTheory.Bass.strictDiagramTelescopeComparison laurentSquareFunctor
    boundedFlatAffineSectionBassDiagram boundedFlatAffineSectionBassTransition

/-- Every original corner separation premise is discharged at every actual finite stage. -/
theorem boundedFlatAffineSectionBassTelescopeComparison_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassTelescopeComparison.app R) :=
  KTheory.Bass.strictDiagramTelescopeComparison_isStableEquivalence laurentSquareFunctor
    boundedFlatAffineSectionBassDiagram boundedFlatAffineSectionBassTransition R

/-- The exact stage inclusion is sent to its unchanged image under the actual Bass functor. -/
theorem boundedFlatAffineSectionBassTelescopeComparison_inclusion (i : ℕ) (R : CommRingCat.{u}) :
    (Telescope.diagramInclusion
        (fun i => KTheory.Bass.strictRingDiagramFunctor.obj (boundedFlatAffineSectionBassDiagram i))
        (fun i => KTheory.Bass.strictRingDiagramFunctor.map
          (boundedFlatAffineSectionBassTransition i)) i).app R ≫
        boundedFlatAffineSectionBassTelescopeComparison.app R =
      (KTheory.Bass.strictRingDiagramFunctor.map
        (boundedFlatAffineSectionBassTelescopeInclusion i)).app R :=
  KTheory.Bass.strictDiagramTelescopeComparison_inclusion laurentSquareFunctor
    boundedFlatAffineSectionBassDiagram boundedFlatAffineSectionBassTransition i R

/-- The original successor map is the exact evaluation of the right-iteration transport. -/
theorem boundedFlatAffineSectionBassSuccessorIso_hom (i : ℕ) :
    (boundedFlatAffineSectionBassSuccessorIso.{u} i).hom =
      eqToHom (congrArg
        (fun H : (CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1}) ⥤
            (CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1}) =>
          H.obj boundedFlatAffineSectionPrespectrumFunctor)
        (KTheory.Bass.strictDiagramIterate_succ_right laurentSquareFunctor i)) := rfl

/-- The original successor comparison transports the same original iterated Laurent seed. -/
theorem boundedFlatAffineSectionBassSuccessorIso_transition (i : ℕ) :
    boundedFlatAffineSectionBassTransition.{u} (i + 1) ≫
        (boundedFlatAffineSectionBassSuccessorIso (i + 1)).hom =
      (boundedFlatAffineSectionBassSuccessorIso i).hom ≫
        KTheory.Bass.strictRingDiagramFunctor.map (boundedFlatAffineSectionBassTransition i) := by
  rw [boundedFlatAffineSectionBassSuccessorIso_hom,
    boundedFlatAffineSectionBassSuccessorIso_hom]
  have h := KTheory.Bass.strictDiagramTransition_succ_right
    (F := boundedFlatAffineSectionPrespectrumFunctor.{u}) laurentSquareFunctor
    boundedFlatAffineSectionBassSeed i
  dsimp only [boundedFlatAffineSectionBassTransition, KTheory.Bass.strictRingDiagramTransition,
    KTheory.Bass.strictRingDiagramFunctor, boundedFlatAffineSectionBassDiagram,
    KTheory.Bass.strictRingDiagramIterate] at h ⊢
  apply NatTrans.ext
  funext R
  exact NatTrans.congr_app h R

/-- The actual telescope starting with stage one and the unchanged original later seeds. -/
def boundedFlatAffineSectionBassSuccessorTelescopeFunctor :
    CommRingCat.{u} ⥤ LoopPrespectrum.{u + 1} :=
  Telescope.diagramFunctor (fun i => boundedFlatAffineSectionBassDiagram (i + 1))
    (fun i => boundedFlatAffineSectionBassTransition (i + 1))

/-- The actual equality-induced successor maps act on every original telescope cylinder. -/
def boundedFlatAffineSectionBassSuccessorTelescopeMap :
    boundedFlatAffineSectionBassSuccessorTelescopeFunctor.{u} ⟶
      boundedFlatAffineSectionBassTransformedTelescopeFunctor where
  app R := Telescope.map
    (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R)
    (fun i => (KTheory.Bass.strictRingDiagramFunctor.obj
      (boundedFlatAffineSectionBassDiagram i)).obj R)
    (fun i => (KTheory.Bass.strictRingDiagramFunctor.map
      (boundedFlatAffineSectionBassTransition i)).app R)
    (fun i => (boundedFlatAffineSectionBassSuccessorIso i).hom.app R)
    (fun i => (NatTrans.congr_app (boundedFlatAffineSectionBassSuccessorIso_transition i) R).symm)
  naturality R S f := by
    apply Telescope.hom_ext
    intro k i s x
    exact congrArg
      (fun y => Telescope.cylinder
        (fun i => (KTheory.Bass.strictRingDiagramFunctor.obj
          (boundedFlatAffineSectionBassDiagram i)).obj S)
        (fun i => (KTheory.Bass.strictRingDiagramFunctor.map
          (boundedFlatAffineSectionBassTransition i)).app S) k i (s, y))
      (congrArg (fun m => m.map k x)
        ((boundedFlatAffineSectionBassSuccessorIso i).hom.naturality f))

/-- The original successor-tower comparison is stable, since its exact stage maps are isos. -/
theorem boundedFlatAffineSectionBassSuccessorTelescopeMap_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassSuccessorTelescopeMap.app R) := by
  let : ∀ i k, T1Space (((KTheory.Bass.strictRingDiagramFunctor.obj
      (boundedFlatAffineSectionBassDiagram i)).obj R).space k) := fun i k =>
    KTheory.Bass.strictDiagramFunctorSpaceT1Space laurentSquareFunctor
      (boundedFlatAffineSectionBassDiagram i) R k
  apply Telescope.map_isStableEquivalence
    (fun i => (boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
    (fun i => (boundedFlatAffineSectionBassTransition (i + 1)).app R)
    (fun i => (KTheory.Bass.strictRingDiagramFunctor.obj
      (boundedFlatAffineSectionBassDiagram i)).obj R)
    (fun i => (KTheory.Bass.strictRingDiagramFunctor.map
      (boundedFlatAffineSectionBassTransition i)).app R)
    (fun i => (boundedFlatAffineSectionBassSuccessorIso i).hom.app R)
    (fun i => (NatTrans.congr_app (boundedFlatAffineSectionBassSuccessorIso_transition i) R).symm)
  intro i d
  change IsIso ((stableHomotopyFunctor d).map
    ((boundedFlatAffineSectionBassSuccessorIso i).app R).hom)
  infer_instance

/-- The original successor-stage face retains the exact equality-induced stage transport. -/
theorem boundedFlatAffineSectionBassSuccessorTelescopeMap_inclusion
    (i : ℕ) (R : CommRingCat.{u}) :
    (Telescope.diagramInclusion (fun i => boundedFlatAffineSectionBassDiagram (i + 1))
        (fun i => boundedFlatAffineSectionBassTransition (i + 1)) i).app R ≫
        boundedFlatAffineSectionBassSuccessorTelescopeMap.app R =
      (boundedFlatAffineSectionBassSuccessorIso i).hom.app R ≫
        (Telescope.diagramInclusion
          (fun i => KTheory.Bass.strictRingDiagramFunctor.obj
            (boundedFlatAffineSectionBassDiagram i))
          (fun i => KTheory.Bass.strictRingDiagramFunctor.map
            (boundedFlatAffineSectionBassTransition i)) i).app R := by
  apply Hom.ext
  funext k
  ext x
  rfl

/-- The unchanged successor-stage telescope maps to Bass of the unchanged original telescope. -/
def boundedFlatAffineSectionBassSuccessorTelescopeComparison :
    boundedFlatAffineSectionBassSuccessorTelescopeFunctor.{u} ⟶
      KTheory.Bass.strictRingDiagramFunctor.obj boundedFlatAffineSectionBassTelescopeFunctor :=
  boundedFlatAffineSectionBassSuccessorTelescopeMap ≫
    boundedFlatAffineSectionBassTelescopeComparison

/-- The actual successor telescope and the actual Bass image are stably equivalent. -/
theorem boundedFlatAffineSectionBassSuccessorTelescopeComparison_isStableEquivalence
    (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R) :=
  (boundedFlatAffineSectionBassSuccessorTelescopeMap_isStableEquivalence R).comp
    (boundedFlatAffineSectionBassTelescopeComparison_isStableEquivalence R)

/-- Its original stage face retains both the true iteration transport and Bass of that inclusion. -/
theorem boundedFlatAffineSectionBassSuccessorTelescopeComparison_inclusion
    (i : ℕ) (R : CommRingCat.{u}) :
    (Telescope.diagramInclusion (fun i => boundedFlatAffineSectionBassDiagram (i + 1))
        (fun i => boundedFlatAffineSectionBassTransition (i + 1)) i).app R ≫
        boundedFlatAffineSectionBassSuccessorTelescopeComparison.app R =
      (boundedFlatAffineSectionBassSuccessorIso i).hom.app R ≫
        (KTheory.Bass.strictRingDiagramFunctor.map
          (boundedFlatAffineSectionBassTelescopeInclusion i)).app R := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ boundedFlatAffineSectionBassTelescopeComparison.app R)
      (boundedFlatAffineSectionBassSuccessorTelescopeMap_inclusion i R)).trans
      ((Category.assoc _ _ _).trans
        (congrArg ((boundedFlatAffineSectionBassSuccessorIso i).hom.app R ≫ ·)
          (boundedFlatAffineSectionBassTelescopeComparison_inclusion i R))))

end Quillen.PerfectComplexes
