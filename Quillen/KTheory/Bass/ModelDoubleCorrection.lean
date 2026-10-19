/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDoubleLaurentSign
public import Quillen.KTheory.Bass.SchemeConjugationSignedShift
public import Quillen.KTheory.Bass.SchemeStageClassComparison

/-!
# The second original correction from the fixed double quotient sign

The actual double-cone permutation sign passes through the full diagram casts
in the prescribed finite word. The two genuine parameter shifts then cancel
its sign with the proved double-loop transpose sign. The sole remaining input
is the independently defined fixed quotient swap sign of the original row.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open Quillen.KTheory.Bass.NormalizedStageMap
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.GeometricConeInterchange
open Quillen.KTheory.Bass.GeometricConeFixedWords
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed

/-- The prescribed whole-word casts preserve the sign of the actual permutation. -/
theorem wordAt_two_zero_neg (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ)
    (h : (stableHomotopyFunctor 0).map (permutation F X).hom = -𝟙 _) :
    (stableHomotopyFunctor 0).map ((wordAt 2 F).hom.app X) = -𝟙 _ := by
  let e : (coneFunctor.obj (coneFunctor.obj F)).obj X ≅
      (FiniteConeTopology.iterate
        AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.squareFunctor 2 F).obj X :=
    (eqToIso (power_obj 2 F)).app X
  have hw : (wordAt 2 F).hom.app X = e.inv ≫ (permutation F X).hom ≫ e.hom :=
    congrArg (fun t => t.app X) (wordAt_two_hom F)
  rw [hw]
  rw [Functor.map_comp, Functor.map_comp, h]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp]
  rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]

private theorem negative_word_identity {A B : AddCommGrpCat.{w}}
    (q : A ⟶ A) (e : A ≅ B) (r : B ⟶ B)
    (hs : q ≫ e.hom = -(e.hom ≫ r)) (hr : r = -𝟙 B) : q = 𝟙 A := by
  apply (cancel_mono e.hom).1
  rw [hs, hr]
  simp only [Preadditive.comp_neg, Category.comp_id, neg_neg, Category.id_comp]

/-- Both actual shifts turn the negative geometric word into the identity correction. -/
theorem conjugatingIso_two_negTwo_id_of_permutation
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (h : (stableHomotopyFunctor 0).map (permutation F X).hom = -𝟙 _) :
    (stableHomotopyFunctor (-2)).map ((conjugatingIso 2 F).hom.app X) = 𝟙 _ := by
  let A := (stableHomotopyFunctor (-2)).obj
    ((normalized AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.squareFunctor 2 F).obj X)
  let B := (stableHomotopyFunctor 0).obj
    ((FiniteConeTopology.iterate
      AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.squareFunctor 2 F).obj X)
  let q : A ⟶ A := (stableHomotopyFunctor (-2)).map ((conjugatingIso 2 F).hom.app X)
  let e : A ≅ B := doubleNormalizedShift F X (-2)
  let r : B ⟶ B := (stableHomotopyFunctor 0).map ((wordAt 2 F).hom.app X)
  have hs : q ≫ e.hom = -(e.hom ≫ r) := conjugatingIso_two_signedShift F X (-2)
  have hr : r = -𝟙 B := wordAt_two_zero_neg F X h
  exact negative_word_identity q e r hs hr

/-- The original second correction is identity once its original fixed quotient swap is negative. -/
theorem conjugatingIso_two_negTwo_id_of_quotient_swap
    (M : Scheme.{u}ᵒᵖ ⥤ Model.{w}) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (M ⋙ prespectrumFunctor)) X = -𝟙 _) :
    (stableHomotopyFunctor (-2)).map
      ((conjugatingIso 2 (M ⋙ prespectrumFunctor)).hom.app (op X.unop.obj)) = 𝟙 _ :=
  conjugatingIso_two_negTwo_id_of_permutation (M ⋙ prespectrumFunctor) (op X.unop.obj)
    (permutation_zero_neg_of_quotient_swap M X h)

private theorem conjugate_identity {A B : AddCommGrpCat.{w}}
    (f : A ⟶ B) [IsIso f] (q : B ⟶ B) (hq : q = 𝟙 B) :
    f ≫ q ≫ inv f = 𝟙 A := by
  rw [hq, Category.id_comp, IsIso.hom_inv_id]

/-- The unchanged finite-stage comparison transports the proved second identity correction. -/
theorem finiteStageStableIso_two_negTwo_id_of_quotient_swap
    (M : Scheme.{u}ᵒᵖ ⥤ Model.{w}) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (M ⋙ prespectrumFunctor)) X = -𝟙 _) :
    (finiteStageStableIso M 2 (op X.unop.obj) (-2)).hom = 𝟙 _ := by
  let H := stableHomotopyFunctor (-2)
  let e := (NormalizedStageMap.stageMap
    AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.squareFunctor 2
      (M ⋙ prespectrumFunctor)).app (op X.unop.obj)
  have : IsIso (H.map e) := model_stageMap_stable
    AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.squareFunctor 2 M
      (op X.unop.obj) (-2)
  exact conjugate_identity (H.map e)
    (H.map ((conjugatingIso 2 (M ⋙ prespectrumFunctor)).hom.app (op X.unop.obj)))
    (conjugatingIso_two_negTwo_id_of_quotient_swap M X h)

end Quillen.KTheory.Bass.SchemeNaturalSeed
