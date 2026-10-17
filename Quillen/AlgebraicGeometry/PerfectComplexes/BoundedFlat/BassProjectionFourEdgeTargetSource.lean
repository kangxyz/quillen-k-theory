/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSourceBeta
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetH0Chart
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt

/-!
# The full source value of the original target tree

The original H0 chart-anchor identity identifies the initial chart node on every genuine
polynomial-reference input. The whole chart-zero identities then combine with the four
original overlap edges to identify the source of the complete target tree with the actual
beta map followed by its full anchored Laurent coefficient node map.
-/
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
open BassH0Merge BassH1Join CommonReferenceNerve CoefficientBassSeedTargetH0Reference

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

private theorem product_chart_total {V A B C D : Model.{u}}
    (E : V ⟶ A) (J : A ⟶ B) (K : B ⟶ C) (L : C ⟶ D)
    (F : A ⟶ C) (Q : A ⟶ D) (H : B ⟶ D)
    (e : F.functor ≅ (J ≫ K).functor) (h : Q.functor ≅ (F ≫ L).functor)
    (δ : H.functor ≅ (K ≫ L).functor) (γ : Q.functor ≅ (J ≫ H).functor)
    (hh : h ≪≫ isoWhiskerRight e L.functor = γ ≪≫ isoWhiskerLeft J.functor δ)
    (N : CommonReferenceNerve.Node (E ≫ J)) :
    CommonReferenceProduct.node (E ≫ Q) (E ≫ J) H (isoWhiskerLeft E.functor γ) N
      ⟨K ≫ L, δ⟩ =
    postReferenceNode (E ≫ Q) L
      (isoWhiskerLeft E.functor h ≪≫ (Functor.associator E.functor F.functor L.functor).symm)
      (postReferenceNode (E ≫ F) K (isoWhiskerLeft E.functor e) N) := by
  have hη :
      (isoWhiskerLeft E.functor h ≪≫
          (Functor.associator E.functor F.functor L.functor).symm) ≪≫
        isoWhiskerRight (isoWhiskerLeft E.functor e) L.functor =
      isoWhiskerLeft E.functor γ ≪≫ isoWhiskerLeft (E ≫ J).functor δ := by
    apply Iso.ext
    ext X
    have he := congrArg (fun i ↦ i.hom.app (E.functor.obj X)) hh
    change h.hom.app (E.functor.obj X) ≫ L.functor.map (e.hom.app (E.functor.obj X)) =
      γ.hom.app (E.functor.obj X) ≫ δ.hom.app (J.functor.obj (E.functor.obj X)) at he
    change (h.hom.app (E.functor.obj X) ≫ 𝟙 _) ≫
      L.functor.map (e.hom.app (E.functor.obj X)) =
        γ.hom.app (E.functor.obj X) ≫ δ.hom.app (J.functor.obj (E.functor.obj X))
    rw [Category.comp_id]
    exact he
  rw [product_total_node]
  rw [post_post_node, hη]

private theorem mapParameter_comp {V W V' W' V'' W'' : Model.{u}}
    {F : V ⟶ W} {G : V' ⟶ W'} {H : V'' ⟶ W''}
    (h : CommonReferenceNerve.Node F → CommonReferenceNerve.Node G)
    (g : CommonReferenceNerve.Node G → CommonReferenceNerve.Node H)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node F))|) :
    mapParameter (fun N ↦ g (h N)) y = mapParameter g (mapParameter h y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  simp only [mapParameter_parameter]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- Every genuine polynomial node retains the full source-boundary chart factorization. -/
theorem chart_source_node (N : CommonReferenceNerve.Node (polynomialReference P a E)) :
    chartNodes P f E α ha N 2 =
      sourceBoundaryNode P f E (chartAttachmentNode P a E α ha N) := by
  have hs : BassH0ChartBoundaryRows.squareNodes P f α 2 =
      (⟨normalizedMap (coefficientMap P (α.app a)) ≫ sourcePost P f,
        BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a))⟩ :
        CommonReferenceNerve.Node (BassH0ChartBoundaryRows.squareSource P f α)) := by
    apply Sigma.ext (Model.Hom.ext rfl)
    apply heq_of_eq
    rfl
  change CommonReferenceProduct.node (E ≫ BassH0Diagram.reference P f)
    (E ≫ normalizedMap (polynomialProjection P a)) (BassH0ChartBoundaryRows.squareSource P f α)
    (isoWhiskerLeft E.functor (BassH0ChartBoundaryRows.canonicalAnchor P f α ha)) N
    (BassH0ChartBoundaryRows.squareNodes P f α 2) =
      postReferenceNode (E ≫ BassH0Diagram.reference P f) (sourcePost P f)
        (isoWhiskerLeft E.functor (h0ProjectionIso P f) ≪≫
          (Functor.associator E.functor (BassProjectionPath.source P a).functor
            (sourcePost P f).functor).symm)
        (postReferenceNode (E ≫ BassProjectionPath.source P a)
          (normalizedMap (coefficientMap P (α.app a)))
          (isoWhiskerLeft E.functor (BassMJoin.projectionEndpointIso P α ha)) N)
  rw [hs]
  exact product_chart_total E (normalizedMap (polynomialProjection P a))
    (normalizedMap (coefficientMap P (α.app a))) (sourcePost P f)
    (BassProjectionPath.source P a) (BassH0Diagram.reference P f)
    (BassH0ChartBoundaryRows.squareSource P f α) (BassMJoin.projectionEndpointIso P α ha)
    (h0ProjectionIso P f)
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a)))
    (BassH0ChartBoundaryRows.canonicalAnchor P f α ha)
    (CoefficientBassSeedTargetH0Chart.h0_chart_total_for P f α ha) N

/-- The initial entire polynomial chart is the actual chart map with its complete target anchor. -/
theorem chart_zero
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|) :
    chart P f E α ha (y, 0) =
      mapParameter (sourceBoundaryNode P f E) (SSet.toTop.map (chartMap P a E α ha) y) := by
  change FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E α ha) (y, NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source, FiniteParameter.parameter_vertex]
  have hn := funext (chart_source_node P f E α ha)
  rw [hn]
  change mapParameter (fun N ↦ sourceBoundaryNode P f E (chartAttachmentNode P a E α ha N)) y =
    mapParameter (sourceBoundaryNode P f E) (mapParameter (chartAttachmentNode P a E α ha) y)
  exact mapParameter_comp (chartAttachmentNode P a E α ha) (sourceBoundaryNode P f E) y

/-- All six complete cells give the actual beta value at the original source of the target tree. -/
theorem tree_source
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    tree P f E (z, 0) =
      mapParameter (sourceBoundaryNode P f E) (SSet.toTop.map (beta P a E) z) := by
  suffices h : (fun z ↦ tree P f E (z, 0)) =
      (fun z ↦ mapParameter (sourceBoundaryNode P f E) (SSet.toTop.map (beta P a E) z)) from
    congrFun h z
  apply FourEdgeTree.funext_cells E (normalizedMap (polynomialProjection P a))
  · intro y
    rw [tree_plus, ← FourEdgeTree.realized_comp, beta_plus]
    exact chart_zero P f E (underToLaurent R) (laurentPlus_projection P a) y
  · intro y
    rw [tree_minus, ← FourEdgeTree.realized_comp, beta_minus]
    exact chart_zero P f E (underToLaurentInvert R) (laurentMinus_projection P a) y
  · exact tree_source_edge12_beta P f E
  · exact tree_source_edge01_beta P f E
  · exact tree_source_edge03_beta P f E
  · exact tree_source_edge34_beta P f E

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
