/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalInputTriangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalLaurentReference

/-! The original target sheet normalization retains the full terminal input attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalTargetTriangle

private theorem target_word {V W A B C : Type u} [Category V] [Category W]
    [Category A] [Category B] [Category C]
    (U : V ⥤ W) (E : W ⥤ A) (J : A ⥤ B) (K : B ⥤ C) (S : A ⥤ C)
    (F : W ⥤ B) (G : W ⥤ C) (ε : S ≅ J ⋙ K)
    (σ : E ⋙ J ≅ F) (τ : E ⋙ S ≅ G) (e : G ≅ F ⋙ K)
    (h : τ ≪≫ e = isoWhiskerLeft E ε ≪≫ isoWhiskerRight σ K) :
    (isoWhiskerLeft U (isoWhiskerLeft E ε) ≪≫
      isoWhiskerLeft U (Functor.associator E J K).symm ≪≫
      (Functor.associator U (E ⋙ J) K).symm) ≪≫
      isoWhiskerRight (isoWhiskerLeft U σ) K =
    isoWhiskerLeft U τ ≪≫ isoWhiskerLeft U e ≪≫
      (Functor.associator U F K).symm := by
  apply Iso.ext
  ext x
  have hx := congrArg (fun z ↦ z.hom.app (U.obj x)) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app] at hx
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app, Category.assoc]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id] | erw [K.map_id]
  exact hx.symm

private theorem target_model {V W A B C : Model.{u}}
    (U : V ⟶ W) (E : W ⟶ A) (J : A ⟶ B) (K : B ⟶ C) (S : A ⟶ C)
    (F : W ⟶ B) (G : W ⟶ C) (ε : S.functor ≅ (J ≫ K).functor)
    (σ : (E ≫ J).functor ≅ F.functor) (τ : (E ≫ S).functor ≅ G.functor)
    (e : G.functor ≅ (F ≫ K).functor)
    (h : τ ≪≫ e = isoWhiskerLeft E.functor ε ≪≫ isoWhiskerRight σ K.functor) :
    @Eq ((U ≫ (E ≫ S)).functor ≅ ((U ≫ F) ≫ K).functor)
      ((isoWhiskerLeft U.functor (isoWhiskerLeft E.functor ε) ≪≫
        isoWhiskerLeft U.functor (Functor.associator E.functor J.functor K.functor).symm ≪≫
        (Functor.associator U.functor (E ≫ J).functor K.functor).symm) ≪≫
        isoWhiskerRight (isoWhiskerLeft U.functor σ) K.functor)
      (isoWhiskerLeft U.functor τ ≪≫ isoWhiskerLeft U.functor e ≪≫
        (Functor.associator U.functor F.functor K.functor).symm) :=
  target_word U.functor E.functor J.functor K.functor S.functor F.functor G.functor ε σ τ e h

open AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open BassH0Merge BassMWholeNerve CoefficientBassSeedCarrierLaurentReference
open CoefficientBassSeedTerminalInputTriangle CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pb" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "qb" => CategoryTheory.NatTrans.app α b
local notation "Ub" => coefficientModel P f
local notation "Eb" => inputReference P pb qb
local notation "Jb" =>
  normalizedMap (polynomialProjection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))
local notation "Kb" =>
  normalizedMap (laurentPlus P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))
local notation "Sb" =>
  BassProjectionPath.source P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "epsb" => BassMJoin.projectionEndpointIso P (underToLaurent R)
  (laurentPlus_projection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))

/-- The complete terminal input attachment joins the original target ordinary sheet. -/
theorem target_normalization :
    targetAttachment P f α ≪≫
      isoWhiskerRight
        (isoWhiskerLeft (Ub).functor
          (CoefficientBassSeedOriginalH0Reference.polynomialIso P pb qb)) (Kb).functor =
    isoWhiskerLeft (Ub).functor (referenceIso P pb qb) ≪≫
      isoWhiskerLeft (Ub).functor (ordinaryAnchor P pb qb) ≪≫
      (Functor.associator (Ub).functor
        (polynomialReference P pb qb).functor (Kb).functor).symm := by
  exact target_model Ub Eb Jb Kb Sb (polynomialReference P pb qb) (laurentReference P pb qb)
    epsb (CoefficientBassSeedOriginalH0Reference.polynomialIso P pb qb) (referenceIso P pb qb)
    (ordinaryAnchor P pb qb) (CoefficientBassSeedOriginalH0Reference.ordinary_triangle P pb qb)

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalTargetTriangle
