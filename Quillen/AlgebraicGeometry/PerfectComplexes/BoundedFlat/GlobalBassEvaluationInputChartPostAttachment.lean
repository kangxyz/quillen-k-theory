/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartReference

/-!
# Complete postcomposed chart attachments

The actual chart projection equation transports the original first evaluation comparison.
All five postcomposed chart nodes then agree with their complete mixed descent references.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex

private theorem post_reference_transport {V W Z : Model.{u}} {ι : Type v}
    (S : ι → (V ⟶ Z)) (T : ι → (V ⟶ W)) (J : W ⟶ Z)
    (e : ∀ i, (S i).functor ≅ (T i ≫ J).functor) {i j : ι} (h : i = j) :
    eqToIso (congrArg (fun a => (S a).functor) h) ≪≫ e j =
      e i ≪≫ isoWhiskerRight
        (eqToIso (congrArg (fun a => (T a).functor) h)) J.functor := by
  subst j
  simp only [eqToIso_refl, Iso.refl_trans, isoWhiskerRight_refl]
  exact (Iso.trans_refl (e i)).symm

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The entire original first comparison is natural under the actual chart equality. -/
theorem post_source_iso :
    chartSourceIso g k hk ≪≫
        evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y) =
      InputMixedDesc.postSourceIso g ≪≫
        isoWhiskerRight
          (eqToIso (congrArg Model.Hom.functor
            (InputChartSimplex.source_eq Y (k.app Y) (hk Y)).symm))
          (evaluationRawMap (laurent.map g)).functor := by
  exact post_reference_transport
    (fun j : laurent.obj Y ⟶ Y =>
      globalModel.map (laurent.map g ≫ j).op ≫ evaluationModel (op (laurent.obj X)))
    (fun j : laurent.obj Y ⟶ Y =>
      globalModel.map j.op ≫ evaluationModel (op (laurent.obj Y)))
    (evaluationRawMap (laurent.map g))
    (fun j => evaluationCompositionFirstIso (laurent.map g) j) (hk Y).symm

/-- All five original Y nodes have exactly the full attached descent anchors. -/
theorem post_nodes (i : Fin 5) : postNode g k hk i =
    InputMixedDesc.postNode g (InputChartSimplex.chartNodes Y (k.app Y) (hk Y) i) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change chartSourceIso g k hk ≪≫
      (evaluationCompositionFirstIso (laurent.map g) (k.app Y ≫ projection.app Y) ≪≫
        isoWhiskerRight (InputSimplex.anchors (k.app Y) (projection.app Y) i)
          (evaluationRawMap (laurent.map g)).functor) = _
  rw [← Iso.trans_assoc, post_source_iso]
  simp only [InputMixedDesc.postNode, CommonReferenceNerve.attachPostcompNode,
    InputChartSimplex.chartNodes, isoWhiskerRight_trans, Iso.trans_assoc]

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
