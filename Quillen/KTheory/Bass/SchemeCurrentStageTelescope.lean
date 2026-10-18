/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeCurrentStageSquare
public import Quillen.Topology.Prespectrum.TelescopeDiagramMap
public import Quillen.Topology.Prespectrum.TelescopeStableEquivalence

/-! # The current-stage to unpermuted normalized telescope comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The actual finite Bass objects with their current-stage seeds. -/
def currentTelescope (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (currentTransition A)

/-- The unpermuted cone-normalized objects with their literal looped current cone seeds. -/
def normalizedTelescope (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => normalized squareFunctor i F) (normalizedTransition A)

/-- The existing finite stage maps descend to a natural map of these two actual telescopes. -/
def telescopeMap (A : Track laurent.op coefficient F) :
    currentTelescope A ⟶ normalizedTelescope A :=
  Telescope.diagramMap (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => normalized squareFunctor i F) (currentTransition A) (normalizedTransition A)
    (fun i => stageMap squareFunctor i F) (fun i => (currentTransition_stageMap A i).symm)

/-- Every original telescope cylinder keeps its stage and entire height. -/
theorem telescopeMap_cylinder (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((telescopeMap A).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (currentTransition A j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (normalizedTransition A j).app X) n i
      (s, ((stageMap squareFunctor i F).app X).map n x) :=
  Telescope.diagramMap_cylinder
    (fun j => (strictDiagramIterate squareFunctor j).obj F)
    (fun j => normalized squareFunctor j F) (currentTransition A) (normalizedTransition A)
    (fun j => stageMap squareFunctor j F)
    (fun j => (currentTransition_stageMap A j).symm) X n i s x

/-- Original finite-stage inclusions commute with the same telescope map. -/
theorem telescopeMap_inclusion (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => (strictDiagramIterate squareFunctor j).obj F)
        (currentTransition A) i ≫ telescopeMap A =
      stageMap squareFunctor i F ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (normalizedTransition A) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Genuine Model input makes this same current-stage telescope map stable on every scheme. -/
theorem model_telescopeMap_stable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((telescopeMap A).app X) := by
  let : ∀ i n, T1Space
      ((((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space squareFunctor i M X n
  let : ∀ i n, T1Space
      ((normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X |>.space n) := by
    intro i n
    rw [normalized_obj]
    exact modelLoopsIterateSpaceT1Space squareFunctor i i M X n
  exact Telescope.map_isStableEquivalence
    (fun i => ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (currentTransition A i).app X)
    (fun i => (normalized squareFunctor i (M ⋙ prespectrumFunctor)).obj X)
    (fun i => (normalizedTransition A i).app X)
    (fun i => (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X)
    (fun i => congrArg (fun η => η.app X) (currentTransition_stageMap A i).symm)
    (fun i => model_stageMap_stable squareFunctor i M X)

end Quillen.KTheory.Bass.SchemeNaturalSeed
