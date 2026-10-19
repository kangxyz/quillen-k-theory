/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeStageClassComparison
public import Quillen.KTheory.Bass.SchemeConjugationLowStages

/-! # The unchanged first two finite classes

The actual finite correction is the identity at stages zero and one. Thus the
original current and iterated inclusions agree through the existing stable
comparison in these two stages, without any assertion about later words.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap

/-- The first finite correction is the identity through the actual normalization map. -/
theorem finiteStageStableIso_one_hom (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) : (finiteStageStableIso M 1 X d).hom = 𝟙 _ := by
  let H := stableHomotopyFunctor d
  let e := (stageMap squareFunctor 1 (M ⋙ prespectrumFunctor)).app X
  let : IsIso (H.map e) := model_stageMap_stable squareFunctor 1 M X d
  change H.map e ≫ H.map ((conjugatingIso 1 (M ⋙ prespectrumFunctor)).hom.app X) ≫
    inv (H.map e) = _
  rw [conjugatingIso_one_hom]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    IsIso.hom_inv_id]
  rfl

/-- Both low-stage inclusions retain their original class without a finite correction. -/
@[reassoc]
theorem currentIteratedStableIso_low_inclusion (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (i : ℕ) (hi : i ≤ 1) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map
        ((Telescope.diagramInclusion
          (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
          (currentTransition A) i).app X) ≫ (currentIteratedStableIso M A X d).hom =
      (stableHomotopyFunctor d).map
        ((Telescope.diagramInclusion
          (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
          (strictDiagramTransition squareFunctor (seed A)) i).app X) := by
  rw [currentIteratedStableIso_inclusion]
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · rw [finiteStageStableIso_zero_hom, Category.id_comp]
  · rw [finiteStageStableIso_one_hom, Category.id_comp]

end Quillen.KTheory.Bass.SchemeNaturalSeed
