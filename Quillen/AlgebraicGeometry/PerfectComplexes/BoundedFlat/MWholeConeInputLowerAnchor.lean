/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialLower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentNodes

/-! The finite-source lower anchor is the original H0 target followed by Laurent composition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve

private theorem lower_word {V W X Y T U : Type u}
    [Category.{v} V] [Category.{v} W] [Category.{v} X]
    [Category.{v} Y] [Category.{v} T] [Category.{v} U]
    (A : V ⥤ W) (B : W ⥤ X) (D : V ⥤ X) (F₀ : X ⥤ Y) (J₀ : Y ⥤ U)
    (C : X ⥤ T) (L : T ⥤ U) (J : W ⥤ T) (H : W ⥤ U) (G : V ⥤ U)
    (a : G ≅ D ⋙ (F₀ ⋙ J₀)) (rho : D ≅ A ⋙ B) (delta : G ≅ A ⋙ H)
    (b : H ≅ B ⋙ (F₀ ⋙ J₀)) (l : (F₀ ⋙ J₀) ≅ C ⋙ L) (k : H ≅ J ⋙ L) (tau : J ≅ B ⋙ C)
    (h : a ≪≫ isoWhiskerRight rho (F₀ ⋙ J₀) = delta ≪≫ isoWhiskerLeft A b ≪≫
      (Functor.associator A B (F₀ ⋙ J₀)).symm)
    (hpair : b ≪≫ Functor.associator B F₀ J₀ ≪≫ isoWhiskerLeft B l = k ≪≫ isoWhiskerRight tau L ≪≫
      Functor.associator B C L) :
    a ≪≫ isoWhiskerLeft D l ≪≫ (Functor.associator D C L).symm =
      delta ≪≫ isoWhiskerLeft A k ≪≫ (Functor.associator A J L).symm ≪≫
        isoWhiskerRight (isoWhiskerLeft A tau ≪≫ (Functor.associator A B C).symm ≪≫
          isoWhiskerRight rho.symm C) L := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun e ↦ e.hom.app x) h
  have hp := congrArg (fun e ↦ e.hom.app (A.obj x)) hpair
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] at hx hp ⊢
  erw [Category.id_comp] at hp
  simp only [L.map_comp]
  apply (cancel_mono ((C ⋙ L).map (rho.hom.app x))).1
  simp only [Category.assoc, Functor.comp_map,
    ← L.map_comp, ← C.map_comp, Iso.inv_hom_id_app, C.map_id]
  have hn := l.hom.naturality (rho.hom.app x)
  change (F₀ ⋙ J₀).map (rho.hom.app x) ≫ l.hom.app (B.obj (A.obj x)) =
    l.hom.app (D.obj x) ≫ L.map (C.map (rho.hom.app x)) at hn
  erw [Category.comp_id]
  rw [← hn, ← Category.assoc, hx, Category.assoc, hp]

private theorem model_comp {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "D" => sourceReference P p
local notation "F" => pairReference P q w
local notation "L" => CoefficientBassLaurentCompositionCarrier.reference P q w
local notation "Sb" => BassProjectionPath.source P b
local notation "Sd" => BassProjectionPath.source P d
local notation "B" => normalizedMap (polynomialProjection P b)
local notation "E" => inputReference P q w
local notation "G" => BassProjectionPath.WholeReference.reference P d (input P p q w)

/-- The exact right-first reference into the original Laurent product at the target of p. -/
def midpointAnchor : (G).functor ≅ ((A ≫ Sb) ≫ L).functor :=
  isoWhiskerRight (TripleLaurent.inputIso P p q w) (Sd).functor ≪≫
    Functor.associator (A).functor (E).functor (Sd).functor ≪≫
    isoWhiskerLeft (A).functor (InputLaurentProduct.pairAnchor P q w) ≪≫
    (Functor.associator (A).functor (Sb).functor (L).functor).symm

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (β.app b) ≫ polynomialProjection P b = laurentProjection P b)
local notation "C" => BassMWholeNerve.coefficientModel P (β.app b)

/-- The original target polynomial square retains the inverse fourth-node anchor before charting. -/
def lowerSurfaceAnchor : (A ≫ Sb).functor ≅ (D ≫ C).functor :=
  isoWhiskerLeft (A).functor (BassMJoin.projectionEndpointIso P β hb) ≪≫
    (Functor.associator (A).functor (B).functor (C).functor).symm ≪≫
    isoWhiskerRight (rightSquareIso P p).symm (C).functor

variable (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "Jd" => BassMWholeNerve.coefficientModel P (β.app d)

private theorem lower_anchor_of_pair
    (hpair : PairProjection.laurentIso P q w β hd ≪≫
      Functor.associator (B).functor (F).functor (Jd).functor ≪≫
      isoWhiskerLeft (B).functor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) =
      InputLaurentProduct.pairAnchor P q w ≪≫
        isoWhiskerRight (BassMJoin.projectionEndpointIso P β hb) (L).functor ≪≫
        Functor.associator (B).functor (C).functor (L).functor) :
    lowerProductAnchor P p q w β hd =
      midpointAnchor P p q w ≪≫ isoWhiskerRight (lowerSurfaceAnchor P p β hb) (L).functor := by
  have h := lower_word (A).functor (B).functor (D).functor (F).functor (Jd).functor
    (C).functor (L).functor (Sb).functor (E ≫ Sd).functor (G).functor
    (laurentAnchor P p q w β hd ≪≫ Functor.associator (D).functor (F).functor (Jd).functor)
    (rightSquareIso P p)
    (isoWhiskerRight (TripleLaurent.inputIso P p q w) (Sd).functor ≪≫
      Functor.associator (A).functor (E).functor (Sd).functor)
    (PairProjection.laurentIso P q w β hd)
    (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w)
    (InputLaurentProduct.pairAnchor P q w) (BassMJoin.projectionEndpointIso P β hb)
    (by simpa only [model_comp, Iso.trans_assoc] using laurent_anchor_node4 P p q w β hd) hpair
  simpa only [lowerProductAnchor, midpointAnchor, lowerSurfaceAnchor,
    model_comp, Iso.trans_assoc] using h

/-- The positive whole lower anchor agrees with the original H0 target product. -/
theorem plus_lower_anchor :
    lowerProductAnchor P p q w (underToLaurent R) (laurentPlus_projection P d) =
      midpointAnchor P p q w ≪≫ isoWhiskerRight
        (lowerSurfaceAnchor P p (underToLaurent R) (laurentPlus_projection P b)) (L).functor := by
  apply lower_anchor_of_pair P p q w (underToLaurent R) (laurentPlus_projection P b)
    (laurentPlus_projection P d)
  rw [PairProjection.laurentIso_chart, PairLowerReference.plus_chart_anchor]
  have h := PairLowerReference.plus_lower_word P q w
  simp only [model_comp, Iso.trans_assoc] at h ⊢
  exact h

/-- The inverse chart keeps its distinct full anchor in the same original product. -/
theorem minus_lower_anchor :
    lowerProductAnchor P p q w (underToLaurentInvert R) (laurentMinus_projection P d) =
      midpointAnchor P p q w ≪≫ isoWhiskerRight
        (lowerSurfaceAnchor P p (underToLaurentInvert R) (laurentMinus_projection P b))
        (L).functor := by
  apply lower_anchor_of_pair P p q w (underToLaurentInvert R) (laurentMinus_projection P b)
    (laurentMinus_projection P d)
  rw [PairProjection.laurentIso_chart, PairLowerReference.minus_chart_anchor]
  have h := PairLowerReference.minus_lower_word P q w
  simp only [model_comp, Iso.trans_assoc] at h ⊢
  exact h

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
