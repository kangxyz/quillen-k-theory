/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalWhiskeredTriangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalOrdinaryTriangle

/-! The genuine terminal input transport crosses the complete target projection attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalInputTriangle

section Word
variable {V W A B P P' T T' : Type u}
  [Category V] [Category W] [Category A] [Category B] [Category P] [Category P']
  [Category T] [Category T']
  (E : V ⥤ A) (U : V ⥤ W) (F : W ⥤ B) (v : A ⥤ B)
  (J : A ⥤ P) (J' : B ⥤ P') (M : P ⥤ P') (K : P' ⥤ T')
  (S : A ⥤ T) (S' : B ⥤ T') (L : T ⥤ T')
  (γ : E ⋙ v ≅ U ⋙ F) (ρ : v ⋙ J' ≅ J ⋙ M) (μ : v ⋙ S' ≅ S ⋙ L)
  (ε : S' ≅ J' ⋙ K)

private def polynomialWord : (E ⋙ J) ⋙ M ≅ U ⋙ (F ⋙ J') :=
  Functor.associator E J M ≪≫ isoWhiskerLeft E ρ.symm ≪≫
    (Functor.associator E v J').symm ≪≫ isoWhiskerRight γ J' ≪≫
    Functor.associator U F J'

private def laurentWord : (E ⋙ S) ⋙ L ≅ U ⋙ (F ⋙ S') :=
  Functor.associator E S L ≪≫ isoWhiskerLeft E μ.symm ≪≫
    (Functor.associator E v S').symm ≪≫ isoWhiskerRight γ S' ≪≫
    Functor.associator U F S'

private def targetWord : U ⋙ (F ⋙ S') ≅ (U ⋙ (F ⋙ J')) ⋙ K :=
  isoWhiskerLeft U (isoWhiskerLeft F ε) ≪≫
    isoWhiskerLeft U (Functor.associator F J' K).symm ≪≫
    (Functor.associator U (F ⋙ J') K).symm

private def actionWord : (E ⋙ S) ⋙ L ≅ ((E ⋙ J) ⋙ M) ⋙ K :=
  Functor.associator E S L ≪≫
    isoWhiskerLeft E (μ.symm ≪≫ isoWhiskerLeft v ε ≪≫
      (Functor.associator v J' K).symm ≪≫ isoWhiskerRight ρ K) ≪≫
    (Functor.associator E (J ⋙ M) K).symm ≪≫
    isoWhiskerRight (Functor.associator E J M).symm K

private theorem input_word :
    actionWord E v J J' M K S S' L ρ μ ε ≪≫
      isoWhiskerRight (polynomialWord E U F v J J' M γ ρ) K =
    laurentWord E U F v S S' L γ μ ≪≫ targetWord U F J' K S' ε := by
  apply Iso.ext
  ext x
  simp only [actionWord, polynomialWord, laurentWord, targetWord, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  erw [(ρ.app (E.obj x)).map_hom_inv_id_assoc K]
  have h := ε.hom.naturality (γ.hom.app x)
  change S'.map (γ.hom.app x) ≫ ε.hom.app (F.obj (U.obj x)) =
    ε.hom.app (v.obj (E.obj x)) ≫ K.map (J'.map (γ.hom.app x)) at h
  rw [← h]

end Word
open Quillen.Waldhausen.IteratedS
section ModelWord
variable {V W A B P P' T T' : Model.{u}}
  (E : V ⟶ A) (U : V ⟶ W) (F : W ⟶ B) (v : A ⟶ B)
  (J : A ⟶ P) (J' : B ⟶ P') (M : P ⟶ P') (K : P' ⟶ T')
  (S : A ⟶ T) (S' : B ⟶ T') (L : T ⟶ T')
  (γ : (E ≫ v).functor ≅ (U ≫ F).functor)
  (ρ : (v ≫ J').functor ≅ (J ≫ M).functor)
  (μ : (v ≫ S').functor ≅ (S ≫ L).functor)
  (ε : S'.functor ≅ (J' ≫ K).functor)

private def modelPolynomial : ((E ≫ J) ≫ M).functor ≅ (U ≫ (F ≫ J')).functor :=
  Functor.associator E.functor J.functor M.functor ≪≫ isoWhiskerLeft E.functor ρ.symm ≪≫
    (Functor.associator E.functor v.functor J'.functor).symm ≪≫
    isoWhiskerRight γ J'.functor ≪≫ Functor.associator U.functor F.functor J'.functor

private def modelLaurent : ((E ≫ S) ≫ L).functor ≅ (U ≫ (F ≫ S')).functor :=
  Functor.associator E.functor S.functor L.functor ≪≫ isoWhiskerLeft E.functor μ.symm ≪≫
    (Functor.associator E.functor v.functor S'.functor).symm ≪≫
    isoWhiskerRight γ S'.functor ≪≫ Functor.associator U.functor F.functor S'.functor

private def modelTarget : (U ≫ (F ≫ S')).functor ≅ ((U ≫ (F ≫ J')) ≫ K).functor :=
  isoWhiskerLeft U.functor (isoWhiskerLeft F.functor ε) ≪≫
    isoWhiskerLeft U.functor (Functor.associator F.functor J'.functor K.functor).symm ≪≫
    (Functor.associator U.functor (F ≫ J').functor K.functor).symm

private def modelAction : ((E ≫ S) ≫ L).functor ≅ (((E ≫ J) ≫ M) ≫ K).functor :=
  Functor.associator E.functor S.functor L.functor ≪≫
    isoWhiskerLeft E.functor (μ.symm ≪≫ isoWhiskerLeft v.functor ε ≪≫
      (Functor.associator v.functor J'.functor K.functor).symm ≪≫
      isoWhiskerRight ρ K.functor) ≪≫
    (Functor.associator E.functor (J ≫ M).functor K.functor).symm ≪≫
    isoWhiskerRight (Functor.associator E.functor J.functor M.functor).symm K.functor

private theorem model_input_word :
    modelAction E v J J' M K S S' L ρ μ ε ≪≫
      isoWhiskerRight (modelPolynomial E U F v J J' M γ ρ) K.functor =
    modelLaurent E U F v S S' L γ μ ≪≫ modelTarget U F J' K S' ε := by
  exact input_word E.functor U.functor F.functor v.functor J.functor J'.functor
    M.functor K.functor S.functor S'.functor L.functor γ ρ μ ε

end ModelWord

open AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS BassH0Merge BassMWholeNerve
open CoefficientBassSeedCarrierLaurentReference CoefficientBassSeedTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "Ea" =>
  inputReference P (CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a)
    (CategoryTheory.NatTrans.app α a)
local notation "Eb" =>
  inputReference P (CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b)
    (CategoryTheory.NatTrans.app α b)
local notation "U" => coefficientModel P f
local notation "v" =>
  normalizedMap (coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f))
local notation "Ja" =>
  normalizedMap (polynomialProjection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) a))
local notation "Jb" =>
  normalizedMap (polynomialProjection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))
local notation "Mf" => M P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "K" => CoefficientBassSeedTargetChartAttachment.Jb P
  (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "Sa" =>
  BassProjectionPath.source P (CategoryTheory.Functor.obj (laurentUnderFunctor R) a)
local notation "Sb" =>
  BassProjectionPath.source P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "Lf" => L P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "gi" => CoefficientBassSeedTerminalInputReference.inputIso P f α
local notation "ri" => CoefficientBassSeedTerminalPolynomialReference.projectionIso P
  (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "li" => CoefficientBassSeedTargetReferenceTransport.projectionIso P
  (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "eps" => BassMJoin.projectionEndpointIso P (underToLaurent R)
  (laurentPlus_projection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))

/-- The polynomial terminal input transport before original sheet reanchoring. -/
def polynomialTransport : ((Ea ≫ Ja) ≫ Mf).functor ≅ (U ≫ (Eb ≫ Jb)).functor :=
  Functor.associator (Ea).functor (Ja).functor (Mf).functor ≪≫
    isoWhiskerLeft (Ea).functor (ri).symm ≪≫
    (Functor.associator (Ea).functor (v).functor (Jb).functor).symm ≪≫
    isoWhiskerRight gi (Jb).functor ≪≫ Functor.associator (U).functor (Eb).functor (Jb).functor

/-- The Laurent part retains the original projection transport and genuine input isomorphism. -/
def laurentTransport : ((Ea ≫ Sa) ≫ Lf).functor ≅ (U ≫ (Eb ≫ Sb)).functor :=
  Functor.associator (Ea).functor (Sa).functor (Lf).functor ≪≫
    isoWhiskerLeft (Ea).functor (li).symm ≪≫
    (Functor.associator (Ea).functor (v).functor (Sb).functor).symm ≪≫
    isoWhiskerRight gi (Sb).functor ≪≫ Functor.associator (U).functor (Eb).functor (Sb).functor

/-- The target attachment retains both source-domain associators. -/
def targetAttachment : (U ≫ (Eb ≫ Sb)).functor ≅ ((U ≫ (Eb ≫ Jb)) ≫ K).functor :=
  isoWhiskerLeft (U).functor (isoWhiskerLeft (Eb).functor eps) ≪≫
    isoWhiskerLeft (U).functor
      (Functor.associator (Eb).functor (Jb).functor (K).functor).symm ≪≫
    (Functor.associator (U).functor (Eb ≫ Jb).functor (K).functor).symm

/-- The actual terminal input isomorphism crosses the complete projection attachment. -/
theorem input_triangle :
    targetAnchor P (CategoryTheory.Functor.map (laurentUnderFunctor R) f) (Ea ≫ Ja) (Ea ≫ Sa)
      (isoWhiskerLeft (Ea).functor (BassMJoin.projectionEndpointIso P (underToLaurent R)
        (laurentPlus_projection P (CategoryTheory.Functor.obj (laurentUnderFunctor R) a)))) ≪≫
      isoWhiskerRight (polynomialTransport P f α) (K).functor =
    laurentTransport P f α ≪≫ targetAttachment P f α := by
  rw [CoefficientBassSeedTerminalWhiskeredTriangle.target_anchor_whisker]
  have h := model_input_word Ea U Eb v Ja Jb Mf K Sa Sb Lf gi ri li eps
  simpa only [modelAction, modelPolynomial, modelLaurent, modelTarget, polynomialTransport,
    laurentTransport, targetAttachment,
    CoefficientBassSeedTerminalProjectionTriangle.projectionAnchor]
    using h

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalInputTriangle
