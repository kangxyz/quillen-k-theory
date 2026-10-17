/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalPolynomialNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalChartJoin

/-! The terminal chart maps on arbitrary genuine polynomial reference nodes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve

private theorem product_total_node {V W T : Model.{u}}
    (F : V ⟶ T) (D : V ⟶ W) (H G : W ⟶ T)
    (γ : F.functor ≅ (D ≫ H).functor) (δ : H.functor ≅ G.functor)
    (N : CommonReferenceNerve.Node D) :
    CommonReferenceProduct.node F D H γ N ⟨G, δ⟩ =
      postReferenceNode F G (γ ≪≫ isoWhiskerLeft D.functor δ) N := by
  have hp : (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (N.2.prod δ) =
      isoWhiskerLeft D.functor δ ≪≫ isoWhiskerRight N.2 G.functor := by
    apply Iso.ext
    ext X
    exact δ.hom.naturality (N.2.hom.app X)
  change (⟨N.1 ≫ G, γ ≪≫ _⟩ : CommonReferenceNerve.Node F) =
    ⟨N.1 ≫ G, (γ ≪≫ isoWhiskerLeft D.functor δ) ≪≫ isoWhiskerRight N.2 G.functor⟩
  rw [hp, Iso.trans_assoc]

private theorem whisker_anchor {V A B C D : Model.{u}}
    (E : V ⟶ A) (J : A ⟶ B) (K : B ⟶ C) (L : C ⟶ D)
    (F : A ⟶ D) (H : B ⟶ D) (G : A ⟶ C)
    (e : G.functor ≅ (J ≫ K).functor) (γ : F.functor ≅ (J ≫ H).functor)
    (δ : H.functor ≅ (K ≫ L).functor) (θ : F.functor ≅ (G ≫ L).functor)
    (h : γ ≪≫ isoWhiskerLeft J.functor δ = θ ≪≫ isoWhiskerRight e L.functor) :
    isoWhiskerLeft E.functor γ ≪≫ isoWhiskerLeft (E ≫ J).functor δ =
      isoWhiskerLeft E.functor θ ≪≫ isoWhiskerRight (isoWhiskerLeft E.functor e) L.functor := by
  apply Iso.ext
  ext X
  exact congrArg (fun η ↦ η.hom.app (E.functor.obj X)) h

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "U" => normalizedMap (coefficientMap P f)
local notation "Pb" => TargetSpan.polynomialPost P f
local notation "H" => CoefficientSquareFamilies.polynomialSource P f

private theorem terminal_chart_node_of_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (h : BassH0ChartBoundaryRows.canonicalAnchor P f α ha ≪≫
      isoWhiskerLeft (Ja).functor (BassH0ChartBoundaryRows.squareNodes P f α 4).2 =
      terminalPolynomialAnchor P f α hb ≪≫
        isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P f 2).2
          (normalizedMap (coefficientMap P (α.app b))).functor)
    (N : CommonReferenceNerve.Node (polynomialReference P a E)) :
    chartNodes P f E α ha N 4 =
      terminalBoundaryNode P f E (chartAttachmentNode P b (E ≫ U) α hb
        (TargetSpan.polynomialMapNode P f E N)) := by
  let K := normalizedMap (coefficientMap P (α.app b))
  let δ := NativeSquareFiveSimplex.sourceIso
    (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a))
    (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap_naturality P α f) ≪≫
      BinaryNormalizationSimplex.total (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map f))
  let e := BinaryNormalizationSimplex.total
    (coefficientMap P ((polynomialUnderFunctor R).map f)) (polynomialProjection P a)
  have hs : BassH0ChartBoundaryRows.squareNodes P f α 4 =
      (⟨Pb ≫ K, δ⟩ : CommonReferenceNerve.Node (BassH0ChartBoundaryRows.squareSource P f α)) := by
    apply Sigma.ext (Model.Hom.ext rfl)
    exact heq_of_eq rfl
  have he : TargetSpan.polynomialMapAnchor P f E =
      TargetSpan.polynomialSquareAnchor P f E ≪≫ isoWhiskerLeft E.functor e := by
    change (_ ≪≫ _) ≪≫ Iso.refl _ = _
    exact Iso.trans_refl _
  change CommonReferenceProduct.node (reference P f E) (polynomialReference P a E)
    (BassH0ChartBoundaryRows.squareSource P f α) (chartAnchor P f E α ha) N
    (BassH0ChartBoundaryRows.squareNodes P f α 4) =
      anchorNode (terminalBoundaryAnchor P f E)
        (postReferenceNode (WholeReference.reference P b (E ≫ U)) K
          (isoWhiskerLeft (E ≫ U).functor (BassMJoin.projectionEndpointIso (c := b) P α hb))
          (postReferenceNode (TargetSpan.polynomialReference P f E) Pb
            (TargetSpan.polynomialMapAnchor P f E) N))
  rw [hs, product_total_node, anchor_post_node, post_post_node, he,
    isoWhiskerRight_trans, ← Iso.trans_assoc, terminal_polynomial_product_anchor]
  apply congrArg (fun η ↦ postReferenceNode (reference P f E) (Pb ≫ K) η N)
  have hh : BassH0ChartBoundaryRows.canonicalAnchor P f α ha ≪≫
      isoWhiskerLeft (Ja).functor δ =
    terminalPolynomialAnchor P f α hb ≪≫ isoWhiskerRight e K.functor := h
  exact whisker_anchor E Ja Pb K (BassH0Diagram.reference P f)
    (BassH0ChartBoundaryRows.squareSource P f α) H e
    (BassH0ChartBoundaryRows.canonicalAnchor P f α ha) δ
    (terminalPolynomialAnchor P f α hb) hh

/-- The entire positive polynomial input keeps its full target reference. -/
theorem chart_terminal_plus_node
    (N : CommonReferenceNerve.Node (polynomialReference P a E)) :
    chartNodes P f E (underToLaurent R) (laurentPlus_projection P a) N 4 =
      terminalBoundaryNode P f E
        (chartAttachmentNode P b (E ≫ U) (underToLaurent R) (laurentPlus_projection P b)
          (TargetSpan.polynomialMapNode P f E N)) :=
  terminal_chart_node_of_anchor P f E (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P b)
    (CoefficientBassSeedTerminalChartJoin.positive_anchor P f) N

/-- The entire inverse polynomial input retains its separate final chart anchor. -/
theorem chart_terminal_minus_node
    (N : CommonReferenceNerve.Node (polynomialReference P a E)) :
    chartNodes P f E (underToLaurentInvert R) (laurentMinus_projection P a) N 4 =
      terminalBoundaryNode P f E
        (chartAttachmentNode P b (E ≫ U) (underToLaurentInvert R) (laurentMinus_projection P b)
          (TargetSpan.polynomialMapNode P f E N)) :=
  terminal_chart_node_of_anchor P f E (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P b)
    (CoefficientBassSeedTerminalChartJoin.negative_anchor P f) N

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
