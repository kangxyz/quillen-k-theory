/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictRingDiagram

/-! Consumers of the closed strict Bass interface and its original polynomial/Laurent square. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.KTheory.Bass Quillen.PolynomialBaseChange
universe u w
namespace QuillenTest.StrictBassDiagram

open Quillen

/-- Both chart maps have their literal original ring homomorphisms. -/
theorem original_charts (R : CommRingCat.{u}) :
    (laurentSquareFunctor.obj R).hom.right = CommRingCat.ofHom Polynomial.toLaurent ∧
      (laurentSquareFunctor.obj R).right.hom = CommRingCat.ofHom
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := ⟨rfl, rfl⟩

/-- A coefficient map acts on all four corners by the original maps. -/
theorem original_coefficients {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (laurentSquareFunctor.map f).left.left = f ∧
      (laurentSquareFunctor.map f).left.right = polynomialMap f ∧
      (laurentSquareFunctor.map f).right.left = polynomialMap f ∧
      (laurentSquareFunctor.map f).right.right = laurentMap f := ⟨rfl, rfl, rfl, rfl⟩

/-- The original pushout cylinder is sent to its actual constant composite at every time. -/
theorem comparison_cylinder (F : CommRingCat.{u} ⥤ LoopPrespectrum.{w})
    (R : CommRingCat.{u}) (n : ℕ) (s : unitInterval)
    (x : (F.obj R).space n) :
    let S := F.mapArrow.mapArrow.obj (laurentSquareFunctor.obj R)
    (LoopPrespectrum.StrictSquare.comparison S).map n
        (LoopPrespectrum.HomotopyPushout.cylinder S.left.hom S.hom.left n (s, x)) =
      (F.map (coefficient R) ≫ F.map (CommRingCat.ofHom Polynomial.toLaurent)).map n x := rfl

/-- Strict identity action remains literal even after two Bass steps. -/
theorem twice_identity (F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}) :
    (strictRingDiagramIterate 2).map (𝟙 F) = 𝟙 ((strictRingDiagramIterate 2).obj F) :=
  (strictRingDiagramIterate 2).map_id F

/-- Every iterate preserves composition of arbitrary strict natural transformations. -/
theorem iterated_composition (n : ℕ) {F G H : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (a : F ⟶ G) (b : G ⟶ H) :
    (strictRingDiagramIterate n).map (a ≫ b) =
      (strictRingDiagramIterate n).map a ≫ (strictRingDiagramIterate n).map b :=
  (strictRingDiagramIterate n).map_comp a b

/-- The first later transition is literally B applied to the supplied seed. -/
theorem first_iterated_seed {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) :
    strictRingDiagramTransition η 1 = strictRingDiagramFunctor.map η := rfl

/-- All stages retain genuine coefficient naturality of the iterated original seed. -/
theorem all_stage_seed_naturality {F : CommRingCat.{u} ⥤ LoopPrespectrum.{w}}
    (η : F ⟶ strictRingDiagramFunctor.obj F) (n : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((strictRingDiagramIterate n).obj F).map f ≫ (strictRingDiagramTransition η n).app S =
      (strictRingDiagramTransition η n).app R ≫
        ((strictRingDiagramIterate (n + 1)).obj F).map f :=
  strictRingDiagramTransition_naturality η n f

end QuillenTest.StrictBassDiagram
