/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.LoopStable
public import Quillen.Topology.Prespectrum.StableLocalization

/-! Reconstructed regression for the actual natural localized loop strength. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open LoopStrength LoopStable
universe u v w
namespace QuillenTest.BassLoopStable
variable {C : Type u} [Category.{v} C]

/-- The original strength components form a natural transformation. -/
def strengthDiagram (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).obj (F ⋙ parameterLoopingFunctor) ⟶
      (strictDiagramFunctor Q).obj F ⋙ parameterLoopingFunctor where
  app := strength Q F
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Path.ext
    funext r
    exact (strictDiagramMapHomotopy_naturality
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F) (evaluation F)
      (evaluation_naturality F) Q f n r x).symm

/-- Every finite Model stage has a natural isomorphism after stable localization. -/
def localizedStrength (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (M : C ⥤ Model.{w}) :
    ((strictDiagramFunctor Q).obj
      (((strictDiagramIterate Q i).obj (M ⋙ prespectrumFunctor)) ⋙
        parameterLoopingFunctor)) ⋙ toStableLocalization ≅
    (((strictDiagramFunctor Q).obj
      ((strictDiagramIterate Q i).obj (M ⋙ prespectrumFunctor))) ⋙
        parameterLoopingFunctor) ⋙ toStableLocalization :=
  NatIso.ofComponents
    (fun X => stableLocalizationIso _ (modelIterate_strength_stable Q i M X))
    (by
      intro X Y f
      simpa only [stableLocalizationIso_hom, Functor.comp_map, ← Functor.map_comp,
        strengthDiagram] using
        congrArg toStableLocalization.map
          ((strengthDiagram Q ((strictDiagramIterate Q i).obj
            (M ⋙ prespectrumFunctor))).naturality f))


end QuillenTest.BassLoopStable
