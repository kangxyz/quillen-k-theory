/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalProjectionTriangle

/-! Complete reference naturality of the prescribed chart target attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalOrdinaryTriangle

private def post {V B B' C D : Type u} [Category V] [Category B] [Category B']
    [Category C] [Category D] (F : V ⥤ B) (G : V ⥤ C) (J : B ⥤ C)
    (L : C ⥤ D) (M : B ⥤ B') (K : B' ⥤ D)
    (e : G ≅ F ⋙ J) (θ : J ⋙ L ≅ M ⋙ K) : G ⋙ L ≅ (F ⋙ M) ⋙ K :=
  isoWhiskerRight e L ≪≫ Functor.associator F J L ≪≫ isoWhiskerLeft F θ ≪≫
    (Functor.associator F M K).symm

private theorem post_naturality {V B B' C D : Type u} [Category V] [Category B]
    [Category B'] [Category C] [Category D]
    (F F' : V ⥤ B) (G G' : V ⥤ C) (J : B ⥤ C)
    (L : C ⥤ D) (M : B ⥤ B') (K : B' ⥤ D)
    (e : G ≅ F ⋙ J) (e' : G' ≅ F' ⋙ J) (θ : J ⋙ L ≅ M ⋙ K)
    (δ : F ≅ F') (τ : G ≅ G') (h : τ ≪≫ e' = e ≪≫ isoWhiskerRight δ J) :
    isoWhiskerRight τ L ≪≫ post F' G' J L M K e' θ =
      post F G J L M K e θ ≪≫ isoWhiskerRight (isoWhiskerRight δ M) K := by
  apply Iso.ext
  ext x
  have hx := congrArg (fun z ↦ z.hom.app x) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app] at hx
  simp only [post, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  have ht := θ.hom.naturality (δ.hom.app x)
  change L.map (J.map (δ.hom.app x)) ≫ θ.hom.app (F'.obj x) =
    θ.hom.app (F.obj x) ≫ K.map (M.map (δ.hom.app x)) at ht
  rw [← ht]
  rw [← L.map_comp_assoc, ← L.map_comp_assoc, hx]

open AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS BassH0Merge
open CoefficientBassSeedCarrierLaurentReference CoefficientBassPositiveC1BoundaryLift
open CoefficientBassSeedTargetChartAttachment
private theorem post_model {V B B' C D : Model.{u}}
    (F F' : V ⟶ B) (G G' : V ⟶ C) (J : B ⟶ C)
    (L : C ⟶ D) (M : B ⟶ B') (K : B' ⟶ D) (H : B ⟶ D)
    (e : G.functor ≅ (F ≫ J).functor) (e' : G'.functor ≅ (F' ≫ J).functor)
    (l : H.functor ≅ (J ≫ L).functor) (r : H.functor ≅ (M ≫ K).functor)
    (δ : F.functor ≅ F'.functor) (τ : G.functor ≅ G'.functor)
    (h : τ ≪≫ e' = e ≪≫ isoWhiskerRight δ J.functor) :
    @Eq ((G ≫ L).functor ≅ ((F' ≫ M) ≫ K).functor)
      (isoWhiskerRight τ L.functor ≪≫
        ((isoWhiskerRight e' L.functor ≪≫ Functor.associator F'.functor J.functor L.functor ≪≫
          isoWhiskerLeft F'.functor l.symm) ≪≫ isoWhiskerLeft F'.functor r ≪≫
          (Functor.associator F'.functor M.functor K.functor).symm))
      (((isoWhiskerRight e L.functor ≪≫ Functor.associator F.functor J.functor L.functor ≪≫
          isoWhiskerLeft F.functor l.symm) ≪≫ isoWhiskerLeft F.functor r ≪≫
          (Functor.associator F.functor M.functor K.functor).symm) ≪≫
        isoWhiskerRight (isoWhiskerRight δ M.functor) K.functor) := by
  simpa only [post, isoWhiskerLeft_trans, Iso.trans_assoc] using
    post_naturality F.functor F'.functor G.functor G'.functor J.functor L.functor
      M.functor K.functor e e' (l.symm ≪≫ r) δ τ h

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c d : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (f : c ⟶ d)

/-- The actual ordinary source normalization commutes with the entire prescribed chart square. -/
theorem source_normalization :
    isoWhiskerRight (referenceIso P p q) (L P f).functor ≪≫
      targetAnchor P f (polynomialReference P p q) (laurentReference P p q)
        (ordinaryAnchor P p q) =
    targetAnchor P f
      (inputReference P p q ≫ normalizedMap (polynomialProjection P c))
      (inputReference P p q ≫ BassProjectionPath.source P c)
      (isoWhiskerLeft (inputReference P p q).functor
        (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c))) ≪≫
      isoWhiskerRight
        (isoWhiskerRight (CoefficientBassSeedOriginalH0Reference.polynomialIso P p q)
          (M P f).functor) (Jb P (b := d)).functor := by
  have h := post_model
    (inputReference P p q ≫ normalizedMap (polynomialProjection P c))
    (polynomialReference P p q)
    (inputReference P p q ≫ BassProjectionPath.source P c)
    (laurentReference P p q) (Ja P (a := c)) (L P f)
    (M P f) (Jb P (b := d)) (H P f)
    (isoWhiskerLeft (inputReference P p q).functor
      (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c)))
    (ordinaryAnchor P p q) (leftIso P f) (rightIso P f)
    (CoefficientBassSeedOriginalH0Reference.polynomialIso P p q) (referenceIso P p q)
    (CoefficientBassSeedOriginalH0Reference.ordinary_triangle P p q)
  exact h

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalOrdinaryTriangle
