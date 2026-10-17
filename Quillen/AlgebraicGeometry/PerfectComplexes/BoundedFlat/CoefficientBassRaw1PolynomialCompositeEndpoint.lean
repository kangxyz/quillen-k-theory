/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairDirectAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointCells

/-! Actual same-sign composite actions on the genuine identity-source polynomial cylinder. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeEndpoint
open CommonReferenceNerve CoefficientBassRaw1PolynomialSourceCylinder

/-- Complete identity-source normalization retains the second precomposed chart node. -/
theorem normalize_second_node {V W U T : Model.{v}}
    (F : V ⟶ U) (M : V ⟶ W) (K : W ⟶ U) (J : U ⟶ T)
    (H : W ⟶ T) (G : V ⟶ T) (η : F.functor ≅ (M ≫ K).functor)
    (θ : G.functor ≅ (((𝟙 V) ≫ M) ≫ H).functor)
    (ρ : H.functor ≅ (K ≫ J).functor) (N : Node H) :
    CommonReferenceProduct.reanchor (F₀ := F ≫ J) (F₁ := G)
      (isoWhiskerRight (η ≪≫ isoWhiskerRight
        (Functor.leftUnitor M.functor).symm K.functor) J.functor ≪≫
        (θ ≪≫ isoWhiskerLeft (((𝟙 V) ≫ M).functor) ρ ≪≫
          (Functor.associator (((𝟙 V) ≫ M).functor) K.functor J.functor).symm).symm)
      (⟨((𝟙 V) ≫ M) ≫ N.1, θ ≪≫
        isoWhiskerLeft (((𝟙 V) ≫ M).functor) N.2 ≪≫
        isoWhiskerRight (isoWhiskerRight (Iso.refl (𝟙 V : V ⟶ V).functor)
          M.functor) N.1.functor⟩ : Node G) =
    BassH0Merge.preReferenceNode (F ≫ J) M
      (isoWhiskerRight η J.functor ≪≫ Functor.associator M.functor K.functor J.functor ≪≫
        isoWhiskerLeft M.functor ρ.symm) N := by
  dsimp only [CommonReferenceProduct.reanchor, BassH0Merge.preReferenceNode]
  apply Sigma.ext
  · exact congrArg (fun Z ↦ Z ≫ N.1) (Category.id_comp M)
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [Iso.trans_symm, Iso.symm_symm_eq, isoWhiskerRight_trans, Iso.trans_assoc,
    isoWhiskerRight_refl, Iso.symm_self_id_assoc, Iso.trans_hom,
    isoWhiskerRight_hom, Iso.symm_hom, isoWhiskerLeft_inv, isoWhiskerLeft_hom,
    NatTrans.comp_app, comp_obj, whiskerRight_app, id_obj, leftUnitor_inv_app,
    CategoryTheory.Functor.map_id, associator_hom_app, whiskerLeft_app]
  change J.functor.map (η.hom.app X) ≫ J.functor.map (𝟙 _) ≫ 𝟙 _ ≫
      ρ.inv.app (M.functor.obj X) ≫ N.2.hom.app (M.functor.obj X) ≫ 𝟙 _ = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact congrArg (fun k ↦ J.functor.map (η.hom.app X) ≫ k)
    (Category.id_comp (ρ.inv.app (M.functor.obj X) ≫ N.2.hom.app (M.functor.obj X))).symm

/-- Complete identity-source normalization retains the first postcomposed chart node. -/
theorem normalize_post_identity_node {V W T : Model.{v}}
    (F : V ⟶ T) (H G : V ⟶ W) (L : W ⟶ T)
    (δ : F.functor ≅ (G ≫ L).functor)
    (θ : G.functor ≅ ((𝟙 V) ≫ H).functor) (N : Node H) :
    CommonReferenceProduct.reanchor δ
      (postcompNode L (⟨(𝟙 V) ≫ N.1, θ ≪≫ isoWhiskerLeft (𝟙 V : V ⟶ V).functor N.2 ≪≫
        isoWhiskerRight (Iso.refl (𝟙 V : V ⟶ V).functor) N.1.functor⟩ : Node G)) =
    BassH1Join.postReferenceNode F L
      (δ ≪≫ isoWhiskerRight θ L.functor ≪≫
        isoWhiskerRight (Functor.leftUnitor H.functor) L.functor) N := by
  dsimp only [CommonReferenceProduct.reanchor, postcompNode, BassH1Join.postReferenceNode]
  apply Sigma.ext
  · exact congrArg (fun Z ↦ Z ≫ L) (Category.id_comp N.1)
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Iso.refl_hom, NatTrans.id_app, comp_obj, id_obj,
    leftUnitor_hom_app, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp,
    Category.comp_id, Category.assoc]
  change δ.hom.app X ≫ L.functor.map (θ.hom.app X) ≫ L.functor.map (N.2.hom.app X) =
    δ.hom.app X ≫ L.functor.map (θ.hom.app X) ≫ 𝟙 _ ≫ L.functor.map (N.2.hom.app X)
  simp only [Category.id_comp]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The exact pair normalization retains the actual source identity and original binary word. -/
def polynomialIso :
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor ≅
      (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
        CoefficientBassSeedTargetChartAttachment.M P q).functor :=
  BinaryNormalizationSimplex.total
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((polynomialUnderFunctor R).map p)) ≪≫
    isoWhiskerRight (Functor.leftUnitor
      (CoefficientBassSeedTargetChartAttachment.M P p).functor).symm
      (CoefficientBassSeedTargetChartAttachment.M P q).functor

/-- The original first plus action supplies the exact second source attachment. -/
abbrev plusFirstAnchor := CoefficientBassSeedTargetChartAttachment.targetAnchor P p
  (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)

/-- The composite plus action performs both actual first-sheet descents before normalization. -/
def plus : C(carrier P (underToLaurent R) a,
    CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q) :=
  (CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
      (plusFirstAnchor P p)) (polynomialIso P p q)).comp
    ((CoefficientBassPositiveTargetSingleSheet.firstMap P q
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
      (plusFirstAnchor P p)).comp
      (CoefficientBassPositiveTargetSingleSheet.firstMap P p (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _)))

/-- The whole composite plus endpoint retains every unchanged original cylinder height. -/
def plusPath : C(I, CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q) :=
  (plus P p q).comp (cylinder P (underToLaurent R) a)

/-- The original first minus action supplies the exact second source attachment. -/
abbrev minusFirstAnchor := CoefficientBassNegativeTargetChartAttachment.targetAnchor P p
  (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)

/-- The composite minus action performs both actual first-sheet descents before normalization. -/
def minus : C(carrier P (underToLaurentInvert R) a,
    CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q) :=
  (CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P p) ≫
      CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p)
      (minusFirstAnchor P p)) (polynomialIso P p q)).comp
    ((CoefficientBassNegativeTargetSingleSheet.firstMap P q
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p)
      (minusFirstAnchor P p)).comp
      (CoefficientBassNegativeTargetSingleSheet.firstMap P p (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _)))

/-- The whole composite minus endpoint retains every unchanged original cylinder height. -/
def minusPath : C(I,
    CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q) :=
  (minus P p q).comp (cylinder P (underToLaurentInvert R) a)

/-- The complete Laurent normalization is the one used by the actual plus sheet map. -/
def plusLaurentIso :=
  isoWhiskerRight (polynomialIso P p q) (CoefficientBassSeedTargetChartAttachment.Jb P (b :=
    c)).functor ≪≫
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
      (plusFirstAnchor P p)).symm

/-- The complete Laurent normalization is the one used by the actual minus sheet map. -/
def minusLaurentIso :=
  isoWhiskerRight (polynomialIso P p q) (CoefficientBassNegativeTargetChartAttachment.Jb P (b :=
    c)).functor ≪≫
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p)
      (minusFirstAnchor P p)).symm

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeEndpoint
