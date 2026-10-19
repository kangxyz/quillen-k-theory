/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedUnitNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPrism
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPreAttachment

/-!
# Complete corner joins of the original mixed evaluation seed

The Laurent square's original postcomposition, strict-precomposition, and raw target corners
are the complete positive-chart nodes. Each equality retains the zero-preserving Model arrow
and the full original anchor, including the actual scheme-square and strict composition
transports. The two strict-precomposition corners also meet their original prism columns.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedCornerNodes
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem reassociate_node {V W T U : Model.{u}}
    (J : V ⟶ W) (E : W ⟶ T) (R : T ⟶ U) (F : V ⟶ U)
    (a : F.functor ≅ (J ≫ (E ≫ R)).functor) :
    (⟨(J ≫ E) ≫ R,
      a ≪≫ (Functor.associator J.functor E.functor R.functor).symm⟩ : Node F) =
      ⟨J ≫ (E ≫ R), a⟩ := by
  apply ModelSimplex.reference_node_eq (Functor.assoc J.functor E.functor R.functor)
  change (a.hom ≫ (Functor.associator J.functor E.functor R.functor).inv) ≫
    (Functor.associator J.functor E.functor R.functor).hom = a.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem reassociate_anchor {V W T U Z : Model.{u}}
    (J : V ⟶ W) (K : W ⟶ T) (E : T ⟶ U) (D : W ⟶ Z) (R : Z ⟶ U)
    (F M : V ⟶ U) (a : F.functor ≅ M.functor)
    (b : M.functor ≅ ((J ≫ K) ≫ E).functor)
    (i : (K ≫ E).functor ≅ (D ≫ R).functor)
    (p : F.functor ≅ (J ≫ (K ≫ E)).functor)
    (q : M.functor ≅ ((J ≫ D) ≫ R).functor)
    (hp : p = a ≪≫ b ≪≫ Functor.associator J.functor K.functor E.functor)
    (hq : q = b ≪≫ Functor.associator J.functor K.functor E.functor ≪≫
      isoWhiskerLeft J.functor i ≪≫
        (Functor.associator J.functor D.functor R.functor).symm) :
    a ≪≫ q = (p ≪≫ isoWhiskerLeft J.functor i) ≪≫
      (Functor.associator J.functor D.functor R.functor).symm := by
  rw [hp, hq]
  simp only [Iso.trans_assoc]

private theorem source_transport {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C) (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.sourceIso p v q w h =
      eqToIso (congrArg (fun k : A ⟶ C =>
        (globalModel.map k.op ≫ evaluationModel (op A)).functor) h) := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem pre_source_anchor :
    InputMixedDesc.preSourceIso g =
      InputCommutingSimplex.sourceIso (laurent.map g)
          (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
          (GlobalRawBass.laurentProjection.naturality g) ≪≫
        eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).functor)
          (globalReindex_comp (GlobalRawBass.laurentProjection.app X) g)) ≪≫
        Functor.associator (globalModel.map g.op).functor
          (globalModel.map (GlobalRawBass.laurentProjection.app X).op).functor
          (evaluationModel (op (laurent.obj X))).functor := by
  unfold InputMixedDesc.preSourceIso
  exact congrArg
    (fun a : (InputMixedDesc.sourceMap g).functor ≅
        (InputSimplex.sourceMap (GlobalRawBass.laurentProjection.app X) g).functor =>
      a ≪≫ eqToIso
        (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).functor)
          (globalReindex_comp (GlobalRawBass.laurentProjection.app X) g)) ≪≫
        Functor.associator (globalModel.map g.op).functor
          (globalModel.map (GlobalRawBass.laurentProjection.app X).op).functor
          (evaluationModel (op (laurent.obj X))).functor)
    (source_transport (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
      (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g)).symm

/-- All five raw square nodes meet their original complete positive-chart rectangle nodes. -/
theorem raw_nodes (i : Fin 5) :
    InputSeedUnitNodes.lower g (InputSeedUnitNodes.rawIndex i) =
      InputChartReference.rawNode g plus GlobalRawBass.plus_projection
        (GlobalRawBass.InputDescNodes.sharedIndex i) := by
  exact (InputSeedUnitNodes.raw_lower_nodes g i).trans
    (GlobalRawBass.InputDescNodes.raw_shared_nodes g plus
      GlobalRawBass.plus_projection i).symm

/-- The first raw target is the original postcomposed total corner, with its full anchor. -/
theorem post_total : InputSeedUnitNodes.lower g 4 =
    InputChartReference.postNode g plus GlobalRawBass.plus_projection 1 :=
  (raw_nodes g 2).trans
    (InputChartReference.post_total_node g plus GlobalRawBass.plus_projection).symm

/-- The postcomposed total corner is also the unchanged original raw rectangle node two. -/
theorem post_raw : InputSeedUnitNodes.lower g 4 =
    InputChartReference.rawNode g plus GlobalRawBass.plus_projection 2 :=
  raw_nodes g 2

set_option maxHeartbeats 400000 in
-- Comparing the fixed Model-arrow and functor presentations of this anchor is conversion-heavy.
private theorem pre_total_anchor :
    InputCommutingSimplex.sourceIso (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) ≪≫
      evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g =
    (InputMixedDesc.preSourceIso g ≪≫
      isoWhiskerLeft (globalModel.map g.op).functor
        (evaluationComparisonIso (GlobalRawBass.laurentProjection.app X))) ≪≫
      (Functor.associator (globalModel.map g.op).functor (evaluationModel (op X)).functor
        (evaluationRawMap (GlobalRawBass.laurentProjection.app X)).functor).symm := by
  refine reassociate_anchor
    (globalModel.map g.op) (globalModel.map (GlobalRawBass.laurentProjection.app X).op)
    (evaluationModel (op (laurent.obj X))) (evaluationModel (op X))
    (evaluationRawMap (GlobalRawBass.laurentProjection.app X))
    (InputMixedDesc.sourceMap g)
    (InputSimplex.sourceMap (GlobalRawBass.laurentProjection.app X) g)
    (InputCommutingSimplex.sourceIso (laurent.map g)
      (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
      (GlobalRawBass.laurentProjection.naturality g))
    (eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).functor)
      (globalReindex_comp (GlobalRawBass.laurentProjection.app X) g)))
    (evaluationComparisonIso (GlobalRawBass.laurentProjection.app X))
    (InputMixedDesc.preSourceIso g)
    (evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g) ?_ ?_
  · exact pre_source_anchor g
  · rfl

/-- The second Laurent cut is the actual strict-precomposed X total evaluation corner. -/
theorem pre_total : InputSeedUnitNodes.lower g 6 =
    InputChartReference.preNode g plus GlobalRawBass.plus_projection 1 := by
  rw [InputChartReference.pre_nodes, InputChartSimplex.chartNodes_one]
  change (⟨((globalModel.map g.op ≫ evaluationModel (op X)) ≫
      evaluationRawMap (GlobalRawBass.laurentProjection.app X)),
    InputCommutingSimplex.sourceIso (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) ≪≫
      evaluationCompositionFirstIso (GlobalRawBass.laurentProjection.app X) g⟩ :
        Node (InputSeedCarrier.laurentRef g)) = _
  rw [pre_total_anchor]
  exact reassociate_node (globalModel.map g.op) (evaluationModel (op X))
    (evaluationRawMap (GlobalRawBass.laurentProjection.app X))
    (InputSeedCarrier.laurentRef g) _

/-- The strict-precomposed total corner is precisely the original prism source. -/
theorem pre_prism : InputSeedUnitNodes.lower g 6 =
    InputChartReference.prismNode g plus GlobalRawBass.plus_projection 0 :=
  (pre_total g).trans
    (InputChartReference.prism_pre_nodes g plus GlobalRawBass.plus_projection 0).symm

/-- The second raw target is the complete original rectangle node fifteen. -/
theorem target_raw : InputSeedUnitNodes.lower g 7 =
    InputChartReference.rawNode g plus GlobalRawBass.plus_projection 15 :=
  raw_nodes g 4

/-- The raw target is precisely the original converted prism source. -/
theorem target_prism : InputSeedUnitNodes.lower g 7 =
    InputChartReference.prismNode g plus GlobalRawBass.plus_projection 3 :=
  (target_raw g).trans
    (InputChartReference.prism_raw_nodes g plus GlobalRawBass.plus_projection 0).symm

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedCornerNodes
