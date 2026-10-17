/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputProjectionWord
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairProjection

/-! The fourth full polynomial source node meets the actual right-first central cap reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceProduct

private theorem product_iso {V W T : Model.{u}} {H₀ H₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : H₀.functor ≅ H₁.functor) (f : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod f) =
      isoWhiskerRight e G₀.functor ≪≫ isoWhiskerLeft H₁.functor f := by
  apply Iso.ext
  rfl

/-- Full product nodes retain a specified source-reference transport word. -/
theorem source_node_transport {U V W T T' : Model.{u}}
    (H : U ⟶ V) (B : V ⟶ W) (F : W ⟶ T) (E : V ⟶ T') (J : T' ⟶ T)
    (D : U ⟶ W) (X : U ⟶ T)
    (a : X.functor ≅ (D ≫ F).functor) (rho : D.functor ≅ (H ≫ B).functor)
    (e : X.functor ≅ ((H ≫ E) ≫ J).functor)
    (b : (E ≫ J).functor ≅ (B ≫ F).functor)
    (h : a ≪≫ isoWhiskerRight rho F.functor = e ≪≫
      Functor.associator H.functor E.functor J.functor ≪≫ isoWhiskerLeft H.functor b ≪≫
      (Functor.associator H.functor B.functor F.functor).symm)
    (M : Node F) :
    reanchor a (node (D ≫ F) D F (Iso.refl _) ⟨H ≫ B, rho⟩ M) =
      reanchor e (precompNode H (reanchor b (precompNode B M))) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change a ≪≫ (Iso.refl _ ≪≫
    (Functor.uncurry.obj (whiskeringLeft U W T)).mapIso (rho.prod M.2)) =
      e ≪≫ isoWhiskerLeft H.functor (b ≪≫ isoWhiskerLeft B.functor M.2)
  rw [product_iso, Iso.refl_trans, ← Iso.trans_assoc, h]
  apply Iso.ext
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The endpoint retains the whole polynomial model and its normalized right-square anchor. -/
theorem source_node4 : CoefficientSquareFamilies.polynomialNodes P p 4 =
    (⟨normalizedMap (coefficientMap P p) ≫ normalizedMap (polynomialProjection P b),
      rightSquareIso P p⟩ : Node (sourceReference P p)) :=
  NativeSquareModelNormalization.nodes_four
    (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P p)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p)

/-- Every full pair node has the same right-first anchor at the actual fourth source node. -/
theorem polynomial_node4 (M : Node (pairReference P q w)) :
    reanchor (polynomialAnchor P p q w)
      (FiniteSourceSheet.polynomialNode (sourceReference P p) (pairReference P q w)
        (CoefficientSquareFamilies.polynomialNodes P p) M 4) =
    reanchor (isoWhiskerRight (TripleLaurent.inputIso P p q w)
      (normalizedMap (polynomialProjection P d)).functor)
      (precompNode (normalizedMap (coefficientMap P p))
        (PairProjection.polynomialNode P q w M)) := by
  unfold FiniteSourceSheet.polynomialNode
  rw [source_node4]
  exact source_node_transport (normalizedMap (coefficientMap P p))
    (normalizedMap (polynomialProjection P b)) (pairReference P q w)
    (inputReference P q w) (normalizedMap (polynomialProjection P d))
    (sourceReference P p) (input P p q w ≫ normalizedMap (polynomialProjection P d))
    (polynomialAnchor P p q w) (rightSquareIso P p)
    (isoWhiskerRight (TripleLaurent.inputIso P p q w)
      (normalizedMap (polynomialProjection P d)).functor)
    (PairLowerReference.polynomialAnchor P q w) (polynomial_anchor_node4 P p q w) M

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
