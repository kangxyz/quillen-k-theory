/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalPolynomialRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalBoundary

/-! Both complete polynomial product rows in the exact terminal target reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve

private theorem whiskered_terminal_anchor {V A B C D : Model.{u}}
    (E : V ⟶ A) (U : A ⟶ B) (J : B ⟶ C) (K : C ⟶ D)
    (F : A ⟶ D) (S : B ⟶ D) (H : A ⟶ C)
    (θ : F.functor ≅ (U ≫ S).functor) (e : S.functor ≅ (J ≫ K).functor)
    (d : (U ≫ J).functor ≅ H.functor) :
    ((isoWhiskerLeft E.functor θ ≪≫
      (Functor.associator E.functor U.functor S.functor).symm) ≪≫
        isoWhiskerLeft (E ≫ U).functor e) ≪≫
      isoWhiskerRight (Functor.associator E.functor U.functor J.functor ≪≫
        isoWhiskerLeft E.functor d) K.functor =
    isoWhiskerLeft E.functor (((θ ≪≫ isoWhiskerLeft U.functor e) ≪≫
      (Functor.associator U.functor J.functor K.functor).symm) ≪≫
        isoWhiskerRight d K.functor) := by
  apply Iso.ext
  ext X
  change ((θ.hom.app (E.functor.obj X) ≫ 𝟙 _) ≫
    e.hom.app (U.functor.obj (E.functor.obj X))) ≫
      K.functor.map (𝟙 _ ≫ d.hom.app (E.functor.obj X)) =
    ((θ.hom.app (E.functor.obj X) ≫ e.hom.app (U.functor.obj (E.functor.obj X))) ≫
      𝟙 _) ≫ K.functor.map (d.hom.app (E.functor.obj X))
  simp only [Category.comp_id, Category.id_comp]

private theorem product_post_reference {V W W' T : Model.{u}}
    (E : V ⟶ W) (H : W ⟶ W') (F : W ⟶ T) (J : W' ⟶ T)
    (θ : F.functor ≅ (H ≫ J).functor)
    (N : CommonReferenceNerve.Node E) (M : CommonReferenceNerve.Node H) :
    CommonReferenceProduct.node (E ≫ F) E F (Iso.refl _) N (postReferenceNode F J θ M) =
      postReferenceNode (E ≫ F) J (isoWhiskerLeft E.functor θ)
        (CommonReferenceProduct.node (E ≫ H) E H (Iso.refl _) N M) := by
  have h₁ := CommonReferenceProduct.node_second_reanchor (E ≫ F) E F (H ≫ J)
    θ (Iso.refl _) N (postcompNode J M)
  have h₂ := CommonReferenceProduct.node_postcomp (E ≫ F) E H J
    (isoWhiskerLeft E.functor θ) N M
  simp only [CommonReferenceProduct.postNode, CommonReferenceProduct.reanchor,
    Iso.refl_trans] at h₁ h₂
  exact h₁.trans h₂

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
local notation "U" => normalizedMap (coefficientMap P f)
local notation "J" => normalizedMap (polynomialProjection P b)
local notation "K" => normalizedMap (coefficientMap P (α.app b))
local notation "H" => CoefficientSquareFamilies.polynomialSource P f

/-- Both target-oriented square anchors keep the same complete terminal reference. -/
theorem terminal_polynomial_product_anchor :
    (terminalBoundaryAnchor P f E ≪≫ isoWhiskerLeft (E ≫ U).functor
      (BassMJoin.projectionEndpointIso (c := b) P α hb)) ≪≫
      isoWhiskerRight (TargetSpan.polynomialSquareAnchor P f E) (K).functor =
    isoWhiskerLeft E.functor (terminalPolynomialAnchor P f α hb) :=
  whiskered_terminal_anchor E U J K (BassH0Diagram.reference P f)
    (BassProjectionPath.source P b) H (terminalBaseAnchor P f)
    (BassMJoin.projectionEndpointIso (c := b) P α hb)
    (TargetSpan.polynomialSquareBaseAnchor P f)

/-- Every genuine square node attaches with the full terminal anchor before realization. -/
theorem terminal_polynomial_product (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    CommonReferenceProduct.node (reference P f E) E (BassH0Diagram.reference P f)
      (Iso.refl _) N (postReferenceNode (BassH0Diagram.reference P f) K
        (terminalPolynomialAnchor P f α hb) (CoefficientSquareFamilies.polynomialNodes P f i)) =
    terminalBoundaryNode P f E
      (chartAttachmentNode P b (E ≫ U) α hb (TargetSpan.polynomialSquareNodes P f E N i)) := by
  rw [product_post_reference]
  change _ = anchorNode (terminalBoundaryAnchor P f E)
    (postReferenceNode (WholeReference.reference P b (E ≫ U)) K
      (isoWhiskerLeft (E ≫ U).functor (BassMJoin.projectionEndpointIso (c := b) P α hb))
      (anchorNode (TargetSpan.polynomialSquareAnchor P f E)
        (CommonReferenceProduct.node (E ≫ H) E H (Iso.refl _) N
          (CoefficientSquareFamilies.polynomialNodes P f i))))
  rw [anchor_post_node, post_anchor_node, terminal_polynomial_product_anchor]

/-- The positive H0 polynomial row equals the entire target polynomial-square attachment. -/
theorem terminal_polynomial_plus_product (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    nodes P f E N (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    terminalBoundaryNode P f E
      (chartAttachmentNode P b (E ≫ U) (underToLaurent R) (laurentPlus_projection P b)
        (TargetSpan.polynomialSquareNodes P f E N i)) := by
  change CommonReferenceProduct.node (reference P f E) E (BassH0Diagram.reference P f)
    (Iso.refl _) N (BassH0Diagram.nodes P f _) = _
  rw [BassH0Diagram.plus_nodes, terminal_polynomial_plus_nodes]
  exact terminal_polynomial_product P f E (underToLaurent R) (laurentPlus_projection P b) N i

/-- The inverse H0 row keeps its own chart while retaining the same full square input. -/
theorem terminal_polynomial_minus_product (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    nodes P f E N (BassH0Diagram.minusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    terminalBoundaryNode P f E
      (chartAttachmentNode P b (E ≫ U) (underToLaurentInvert R) (laurentMinus_projection P b)
        (TargetSpan.polynomialSquareNodes P f E N i)) := by
  change CommonReferenceProduct.node (reference P f E) E (BassH0Diagram.reference P f)
    (Iso.refl _) N (BassH0Diagram.nodes P f _) = _
  rw [BassH0Diagram.minus_nodes, terminal_polynomial_minus_nodes]
  exact terminal_polynomial_product P f E (underToLaurentInvert R)
    (laurentMinus_projection P b) N i

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
