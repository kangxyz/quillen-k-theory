/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeStageClassComparison

/-! # Input naturality of the full finite stable correction

The finite correction is natural for every actual input transformation, hence
in particular for the equivariant transformations used in the telescope maps.
No extra equivariance assumption is needed at this finite-object level.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap

/-- The genuine finite word is natural in arbitrary original Model-spectrum input maps. -/
@[reassoc]
theorem finiteStageStableIso_naturality
    (M N : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (η : M ⋙ prespectrumFunctor ⟶ N ⋙ prespectrumFunctor)
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map (((strictDiagramIterate squareFunctor i).map η).app X) ≫
        (finiteStageStableIso N i X d).hom =
      (finiteStageStableIso M i X d).hom ≫
        (stableHomotopyFunctor d).map (((strictDiagramIterate squareFunctor i).map η).app X) := by
  let H := stableHomotopyFunctor d
  let eM := (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X
  let eN := (stageMap squareFunctor i (N ⋙ prespectrumFunctor)).app X
  let : IsIso (H.map eM) := model_stageMap_stable squareFunctor i M X d
  let : IsIso (H.map eN) := model_stageMap_stable squareFunctor i N X d
  have he := congrArg H.map
    (congrArg (fun t => t.app X) (stageMap_naturality squareFunctor i η))
  have hq := congrArg H.map
    (congrArg (fun t => t.app X) (conjugatingIso_naturality i η))
  simp only [NatTrans.comp_app, Functor.map_comp] at he hq
  change H.map _ ≫ H.map eN = H.map eM ≫ H.map _ at he
  change H.map _ ≫ (H.map eN ≫ H.map _ ≫ inv (H.map eN)) =
    (H.map eM ≫ H.map _ ≫ inv (H.map eM)) ≫ H.map _
  apply (cancel_mono (H.map eN)).1
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id, Category.comp_id, he]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← Category.assoc, he, Category.assoc]
  exact congrArg (fun z => H.map eM ≫ z) hq

end Quillen.KTheory.Bass.SchemeNaturalSeed
