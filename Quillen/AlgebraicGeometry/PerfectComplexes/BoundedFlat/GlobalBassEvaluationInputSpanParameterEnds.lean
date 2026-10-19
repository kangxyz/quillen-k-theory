/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterEdges
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartFaceNodes

/-!
# The complete chart target of the original projection square

The original polynomial evaluation carries a complete source-node identification to the
opposite full endpoint. Both strict source transport and raw postcomposition are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterEdges
open GlobalSectionChangeIndex

attribute [local irreducible] evaluationComparisonIso evaluationCompositionTargetIso

/-- Actual raw postcomposition retains the original first evaluation and strict source transport. -/
private theorem first_post_hom {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    {T : Model.{u + 1}} (J : modelOf (boundedFlatPerfectWaldhausen A) ⟶ T)
    (e : (InputSimplex.sourceMap f g ≫ J).functor =
      (globalModel.map g.op ≫
        ((globalModel.map f.op ≫ evaluationModel (op A)) ≫ J)).functor) :
    (isoWhiskerRight (evaluationCompositionFirstIso f g) J.functor).hom =
      eqToHom e ≫
        (isoWhiskerLeft (globalModel.map g.op).functor
          (isoWhiskerRight (evaluationComparisonIso f) J.functor)).hom := by
  apply NatTrans.ext
  funext x
  simp only [evaluationCompositionFirstIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, CategoryTheory.Functor.map_comp,
    eqToIso.hom, eqToHom_app, eqToHom_map]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem post_initial {V W T : Model.{u}} (F G : V ⟶ W) (J : W ⟶ T)
    (R : V ⟶ T) (e : R.functor ≅ (F ≫ J).functor) (a : F.functor ≅ G.functor) :
    (e ≪≫ isoWhiskerRight (Iso.refl F.functor) J.functor) ≪≫
      isoWhiskerRight a J.functor = e ≪≫ isoWhiskerRight a J.functor := by
  rw [isoWhiskerRight_refl]
  exact congrArg (fun α : R.functor ≅ (F ≫ J).functor =>
    α ≪≫ isoWhiskerRight a J.functor) (Iso.trans_refl e)

private theorem pre_reanchor_bridge {V W T : Model.{u}} (P : V ⟶ W)
    (F G H : W ⟶ T) (R : V ⟶ T) (ρ : R.functor ≅ (P ≫ F).functor)
    (a : F.functor ≅ G.functor) (b : G.functor ≅ H.functor) (c : F.functor ≅ H.functor)
    (h : a ≪≫ b = c) :
    (ρ ≪≫ isoWhiskerLeft P.functor a) ≪≫ isoWhiskerLeft P.functor b =
      ρ ≪≫ isoWhiskerLeft P.functor c := by
  rw [Iso.trans_assoc, ← isoWhiskerLeft_trans, h]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private theorem node_anchor_hom_congr {V W : Model.{u}} {F : V ⟶ W}
    {N M : CommonReferenceNerve.Node F} (e : N = M)
    (h : N.1.functor = M.1.functor) : N.2.hom ≫ eqToHom h = M.2.hom := by
  cases e
  simp

private theorem transport_endpoint {V W : Model.{u}} (F : V ⟶ W)
    (N M P Q : CommonReferenceNerve.Node F)
    (e : N.1.functor = M.1.functor) (f : P.1.functor = Q.1.functor)
    (a : N.1.functor ≅ P.1.functor) (b : M.1.functor ≅ Q.1.functor)
    (h : N = M) (ha : N.2 ≪≫ a = P.2) (hb : M.2 ≪≫ b = Q.2)
    (hab : a.hom ≫ eqToHom f = eqToHom e ≫ b.hom) : P = Q := by
  apply ModelSimplex.reference_node_eq f
  calc
    P.2.hom ≫ eqToHom f = (N.2.hom ≫ a.hom) ≫ eqToHom f :=
      congrArg (fun z => z ≫ eqToHom f) (congrArg Iso.hom ha).symm
    _ = (N.2.hom ≫ eqToHom e) ≫ b.hom := by
      rw [Category.assoc, hab, ← Category.assoc]
    _ = M.2.hom ≫ b.hom :=
      congrArg (fun z => z ≫ b.hom) (node_anchor_hom_congr h e)
    _ = Q.2.hom := congrArg Iso.hom hb

set_option backward.isDefEq.respectTransparency true in
private theorem projection_first_bridge :
    (InputSpanParameterNodes.nodes g k hk 0).2 ≪≫
      isoWhiskerRight (evaluationCompositionFirstIso (polynomial.map g) (projection.app Y))
        (evaluationRawMap (k.app X)).functor =
      (InputSpanParameterNodes.nodes g k hk 3).2 := by
  exact post_initial (InputSpanParameterNodes.projectionSource g)
    (InputSimplex.cutMap (polynomial.map g) (projection.app Y))
    (evaluationRawMap (k.app X)) (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.sourceIso g k hk)
    (evaluationCompositionFirstIso (polynomial.map g) (projection.app Y))

private theorem commuting_cut_bridge {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    (InputCommutingSimplex.secondNodes p v q w h 3).2 ≪≫
      evaluationCompositionSecondIso q w =
      (InputCommutingSimplex.secondNodes p v q w h 4).2 := by
  change (InputCommutingSimplex.sourceIso p v q w h ≪≫
    evaluationCompositionFirstIso q w) ≪≫ evaluationCompositionSecondIso q w =
      InputCommutingSimplex.sourceIso p v q w h ≪≫
        (evaluationComparisonIso (q ≫ w) ≪≫ evaluationCompositionTargetIso q w)
  rw [Iso.trans_assoc]
  exact congrArg (fun e => InputCommutingSimplex.sourceIso p v q w h ≪≫ e)
    (Iso.ext (evaluationComposition_pasting q w).symm)

set_option backward.isDefEq.respectTransparency true in
private theorem chart_right_bridge :
    (InputChartSquareParameter.nodes g k hk 6).2 ≪≫
      isoWhiskerLeft (globalModel.map (projection.app Y).op).functor
        (evaluationCompositionSecondIso (k.app X) (polynomial.map g)) =
      (InputChartSquareParameter.nodes g k hk 7).2 := by
  exact pre_reanchor_bridge (globalModel.map (projection.app Y).op)
    (InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y))
    (InputSimplex.cutMap (k.app X) (polynomial.map g))
    (InputSimplex.targetMap (k.app X) (polynomial.map g))
    (InputMixedDesc.sourceMap g) (InputChartSquareParameter.sourceIso g k hk)
    (InputCommutingSimplex.secondNodes (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g) 3).2
    (evaluationCompositionSecondIso (k.app X) (polynomial.map g))
    (InputCommutingSimplex.secondNodes (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g) 4).2
    (commuting_cut_bridge (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g))

set_option backward.isDefEq.respectTransparency true in
/-- The actual polynomial evaluation propagates the full original source-node equality. -/
private theorem projection_chart_target_of_source
    (h : InputSpanParameterNodes.nodes g k hk 0 = InputChartSquareParameter.nodes g k hk 6) :
    InputSpanParameterNodes.nodes g k hk 3 = InputChartSquareParameter.nodes g k hk 7 := by
  let e := congrArg (fun N : CommonReferenceNerve.Node (InputMixedDesc.sourceMap g) =>
    N.1.functor) h
  exact transport_endpoint (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk 0) (InputChartSquareParameter.nodes g k hk 6)
    (InputSpanParameterNodes.nodes g k hk 3) (InputChartSquareParameter.nodes g k hk 7)
    e (by rfl)
    (isoWhiskerRight
      (evaluationCompositionFirstIso (polynomial.map g) (projection.app Y))
      (evaluationRawMap (k.app X)).functor)
    (isoWhiskerLeft (globalModel.map (projection.app Y).op).functor
      (evaluationCompositionSecondIso (k.app X) (polynomial.map g))) h
    (projection_first_bridge g k hk) (chart_right_bridge g k hk)
    ((Category.comp_id _).trans
      (first_post_hom (polynomial.map g) (projection.app Y) (evaluationRawMap (k.app X)) e))

/-- The actual chart-postcomposed projection reaches the full original chart target node. -/
theorem projection_chart_target : InputSpanParameterNodes.nodes g k hk 3 =
    InputChartSquareParameter.nodes g k hk 7 :=
  projection_chart_target_of_source g k hk
    ((projection_pre_source g k hk).trans (InputChartFaceNodes.pre_target_node g k hk).symm)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterEdges
