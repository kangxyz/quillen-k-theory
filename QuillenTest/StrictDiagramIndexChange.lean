/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexTelescope

/-! # Complete finite-stage and quotient-cylinder index-change regressions -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.KTheory.Bass.StrictDiagramIndexChange
universe u₁ v₁ u₂ v₂ w
namespace QuillenTest.StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow) (F : D ⥤ LoopPrespectrum.{w})

/-- At the first actual Bass stage the entire prescribed index square is applied. -/
theorem firstStage (X : C) :
    (iterateIso K Q₁ Q₂ α 1 F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (α.hom.app X)) := rfl

/-- The second stage has precisely the chosen inner-then-outer comparison order. -/
theorem secondStage :
    (iterateIso K Q₁ Q₂ α 2 F).hom =
      (iso K Q₁ Q₂ α ((strictDiagramFunctor Q₂).obj F)).hom ≫
        (strictDiagramFunctor Q₁).map (iso K Q₁ Q₂ α F).hom := rfl

variable (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : K ⋙ F ⟶ (strictDiagramFunctor Q₁).obj (K ⋙ F))
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom = η₁)

/-- The whole first-stage telescope cylinder retains both its height and original square map. -/
theorem firstCylinder (X : C) (n : ℕ) (s : unitInterval)
    (x : (((strictDiagramFunctor Q₂).obj F).obj (K.obj X)).space n) :
    ((telescopeMap K Q₁ Q₂ α η₂ η₁ hseed).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
        (fun j => (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n 1 (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj (K ⋙ F)).obj X)
      (fun j => (strictDiagramTransition Q₁ η₁ j).app X) n 1
      (s, (strictSquareLoopedConeFunctor.map
        (F.mapArrow.mapArrow.map (α.hom.app X))).map n x) := rfl

/-- Every whole quotient point is restored by the specified inverse, at every level. -/
theorem roundTrip (X : C) (n : ℕ) (x : ((telescope Q₂ η₂).obj (K.obj X)).space n) :
    ((telescopeInv K Q₁ Q₂ α η₂ η₁ hseed).app X).map n
      (((telescopeMap K Q₁ Q₂ α η₂ η₁ hseed).app X).map n x) = x :=
  congrArg (fun a => (a.app X).map n x) (telescopeMap_inv K Q₁ Q₂ α η₂ η₁ hseed)

#print axioms StrictDiagramIndexChange.iso_naturality
#print axioms StrictDiagramIndexChange.iterateIso_naturality
#print axioms StrictDiagramIndexChange.transition_square
#print axioms StrictDiagramIndexChange.inverse_transition_square
#print axioms StrictDiagramIndexChange.telescopeIso
#print axioms StrictDiagramIndexChange.telescopeMap_stable

end QuillenTest.StrictDiagramIndexChange
