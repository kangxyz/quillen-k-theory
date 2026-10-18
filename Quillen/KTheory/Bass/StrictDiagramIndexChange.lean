/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagram

/-!
# Change of index for the original strict Bass functor

An actual isomorphism of the four-corner index diagrams induces an isomorphism
between restriction of the original Bass functor and Bass of the restricted diagram.
The prescribed forward index isomorphism acts on the entire original cone and loop.
Naturality holds for every spectrum diagram transformation. No seed or higher
coherence condition is used in this construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace Quillen.KTheory.Bass.StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)

/-- Restrict an actual prespectrum diagram along the specified index functor. -/
def restriction : (D ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) :=
  (Functor.whiskeringLeft C D LoopPrespectrum).obj K

/-- The full source functor of the whiskered index isomorphism. -/
theorem source_eq (F : D ⥤ LoopPrespectrum.{w}) :
    K ⋙ (strictDiagramFunctor Q₂).obj F =
      (K ⋙ Q₂) ⋙ (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor) := rfl

/-- The full target retains composition on both arrow levels and functor association. -/
theorem target_eq (F : D ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q₁).obj (K ⋙ F) =
      (Q₁ ⋙ K.mapArrow.mapArrow) ⋙
        (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor) := rfl

/-- Apply the given forward index isomorphism to the original whole Bass construction. -/
def iso (F : D ⥤ LoopPrespectrum.{w}) :
    K ⋙ (strictDiagramFunctor Q₂).obj F ≅ (strictDiagramFunctor Q₁).obj (K ⋙ F) :=
  Functor.isoWhiskerRight α (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor)

/-- The actual map uses the prescribed four-corner arrow, with its original orientation. -/
theorem iso_hom_app (F : D ⥤ LoopPrespectrum.{w}) (X : C) :
    (iso K Q₁ Q₂ α F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (α.hom.app X)) := rfl

/-- The inverse uses the specified inverse four-corner arrow. -/
theorem iso_inv_app (F : D ⥤ LoopPrespectrum.{w}) (X : C) :
    (iso K Q₁ Q₂ α F).inv.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (α.inv.app X)) := rfl

/-- Index transport is natural in every complete prespectrum diagram map. -/
theorem iso_naturality {F G : D ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    Functor.whiskerLeft K ((strictDiagramFunctor Q₂).map η) ≫ (iso K Q₁ Q₂ α G).hom =
      (iso K Q₁ Q₂ α F).hom ≫
        (strictDiagramFunctor Q₁).map (Functor.whiskerLeft K η) := by
  apply NatTrans.ext
  funext X
  let T := (Functor.mapArrowFunctor (Arrow D) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor D LoopPrespectrum.{w}).map η)
  have h := congrArg strictSquareLoopedConeFunctor.map (T.naturality (α.hom.app X))
  simp only [Functor.map_comp] at h
  exact h.symm

/-- The actual Bass/index interchange is a natural isomorphism of diagram functors. -/
def functorIso :
    strictDiagramFunctor Q₂ ⋙ restriction K ≅ restriction K ⋙ strictDiagramFunctor Q₁ :=
  NatIso.ofComponents (iso K Q₁ Q₂ α) (fun η => iso_naturality K Q₁ Q₂ α η)

end Quillen.KTheory.Bass.StrictDiagramIndexChange
