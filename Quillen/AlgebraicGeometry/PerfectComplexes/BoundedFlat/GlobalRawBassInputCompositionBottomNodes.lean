/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionBottomReferences

/-!
# Six full original chart/bottom nodes for global input composition

Both original source anchors propagate through the Laurent geometric and normalization
transformations. The resulting equalities retain the complete dependent nodes, including their
specified references, and hence can identify whole carrier edges rather than only native values.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes.BassReferenceMerge
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomNodes
open InputCompositionBottomReferences

private theorem pair_row_step {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {K : C ⥤ E}
    (a : K ≅ F₀ ⋙ G₀) (e : F₀ ≅ F₁) (f : G₀ ≅ G₁) :
    a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod (Iso.refl G₀))) ≪≫
        isoWhiskerLeft F₁ f := by
  rw [composition_pair_iso, composition_pair_iso, isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.trans_assoc]

private theorem full_node_eq {V W : Model.{u}} {F : V ⟶ W}
    (N M : CommonReferenceNerve.Node F) (hf : N.1.functor = M.1.functor)
    (hr : HEq N.2 M.2) : N = M :=
  Sigma.ext (Model.Hom.ext hf) hr

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual first Laurent normalization step under the original chart/projection target. -/
abbrev firstStep (k : laurent.obj Z ⟶ polynomial.obj Z) :=
  isoWhiskerLeft (BinaryNormalizationSimplex.targetMap k (projection.app Z)).functor
    (BinaryNormalizationSimplex.first (laurent.map f) (laurent.map g))

/-- The actual total Laurent normalization under the same original target functor. -/
abbrev totalStep (k : laurent.obj Z ⟶ polynomial.obj Z) :=
  isoWhiskerLeft (BinaryNormalizationSimplex.targetMap k (projection.app Z)).functor
    (BinaryNormalizationSimplex.total (laurent.map f) (laurent.map g))

/-- The full chart intermediate reference follows the original first normalization component. -/
theorem chart_first_step (k : laurent ⟶ polynomial)
    (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V) :
    (InputCompositionCarrierCharts.chartNodes f g k hk 16).2 =
      (InputCompositionCarrierCharts.chartNodes f g k hk 15).2 ≪≫
        firstStep f g (k.app Z) := by
  have hs : (rawChartNodes f g k 16).2 =
      (rawChartNodes f g k 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback (k.app Z))
          (BinaryNormalizationSimplex.geometricIso
            (laurent.map f) (laurent.map g))) :=
    last_intermediate_reference _ _ _ _ _ _ _ _ _
  change InputCompositionCarrierCharts.chartReferenceIso f g k hk ≪≫
    isoWhiskerLeft (InputCompositionCarrierCharts.projectionMap (Z := Z)).functor
      (rawChartNodes f g k 16).2 =
    (InputCompositionCarrierCharts.chartReferenceIso f g k hk ≪≫
      isoWhiskerLeft (InputCompositionCarrierCharts.projectionMap (Z := Z)).functor
        (rawChartNodes f g k 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

/-- The full chart endpoint reference follows the original total normalized component. -/
theorem chart_total_step (k : laurent ⟶ polynomial)
    (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V) :
    (InputCompositionCarrierCharts.chartNodes f g k hk 17).2 =
      (InputCompositionCarrierCharts.chartNodes f g k hk 15).2 ≪≫
        totalStep f g (k.app Z) := by
  have hs : (rawChartNodes f g k 17).2 =
      (rawChartNodes f g k 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback (k.app Z))
          (boundedFlatNormalizedPullbackCompIso
            (laurent.map f) (laurent.map g))) :=
    last_target_reference _ _ _ _ _ _ _ _ _
  change InputCompositionCarrierCharts.chartReferenceIso f g k hk ≪≫
    isoWhiskerLeft (InputCompositionCarrierCharts.projectionMap (Z := Z)).functor
      (rawChartNodes f g k 17).2 =
    (InputCompositionCarrierCharts.chartReferenceIso f g k hk ≪≫
      isoWhiskerLeft (InputCompositionCarrierCharts.projectionMap (Z := Z)).functor
        (rawChartNodes f g k 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

/-- The original plus bottom reference follows the first Laurent step. -/
theorem bottom_plus_first_step : (InputCompositionCarrierBottom.nodes f g 7).2 =
    (InputCompositionCarrierBottom.nodes f g 6).2 ≪≫ firstStep f g (plus.app Z) :=
  pair_row_step (InputCompositionCarrierBottom.sourceIso f g)
    (InputIdentityProjection.nodes Z 2).2
    (BinaryNormalizationSimplex.first
      (laurent.map f) (laurent.map g))

/-- The original plus bottom reference follows the total Laurent step. -/
theorem bottom_plus_total_step : (InputCompositionCarrierBottom.nodes f g 8).2 =
    (InputCompositionCarrierBottom.nodes f g 6).2 ≪≫ totalStep f g (plus.app Z) :=
  pair_row_step (InputCompositionCarrierBottom.sourceIso f g)
    (InputIdentityProjection.nodes Z 2).2
    (BinaryNormalizationSimplex.total
      (laurent.map f) (laurent.map g))

/-- The original minus bottom reference follows the first Laurent step. -/
theorem bottom_minus_first_step : (InputCompositionCarrierBottom.nodes f g 13).2 =
    (InputCompositionCarrierBottom.nodes f g 12).2 ≪≫ firstStep f g (minus.app Z) :=
  pair_row_step (InputCompositionCarrierBottom.sourceIso f g)
    (InputIdentityProjection.nodes Z 4).2
    (BinaryNormalizationSimplex.first
      (laurent.map f) (laurent.map g))

/-- The original minus bottom reference follows the total Laurent step. -/
theorem bottom_minus_total_step : (InputCompositionCarrierBottom.nodes f g 14).2 =
    (InputCompositionCarrierBottom.nodes f g 12).2 ≪≫ totalStep f g (minus.app Z) :=
  pair_row_step (InputCompositionCarrierBottom.sourceIso f g)
    (InputIdentityProjection.nodes Z 4).2
    (BinaryNormalizationSimplex.total
      (laurent.map f) (laurent.map g))

/-- The complete original plus intermediate references agree. -/
theorem plus_intermediate_reference :
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 16).2 =
    (InputCompositionCarrierBottom.nodes f g 7).2 := by
  rw [chart_first_step, bottom_plus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep f g (plus.app Z)) (plus_source_reference f g)

/-- The complete original plus target references agree. -/
theorem plus_target_reference :
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 17).2 =
    (InputCompositionCarrierBottom.nodes f g 8).2 := by
  rw [chart_total_step, bottom_plus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep f g (plus.app Z)) (plus_source_reference f g)

/-- The complete original minus intermediate references agree. -/
theorem minus_intermediate_reference :
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 16).2 =
    (InputCompositionCarrierBottom.nodes f g 13).2 := by
  rw [chart_first_step, bottom_minus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep f g (minus.app Z)) (minus_source_reference f g)

/-- The complete original minus target references agree. -/
theorem minus_target_reference :
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 17).2 =
    (InputCompositionCarrierBottom.nodes f g 14).2 := by
  rw [chart_total_step, bottom_minus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep f g (minus.app Z)) (minus_source_reference f g)

/-- The complete original plus source node, including its chosen anchor. -/
theorem plus_source_node :
    InputCompositionCarrierCharts.chartNodes f g plus plus_projection 15 =
      InputCompositionCarrierBottom.nodes f g 6 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 15)
    (InputCompositionCarrierBottom.nodes f g 6) rfl
      (heq_of_eq (InputCompositionBottomReferences.plus_source_reference f g))

/-- The complete original plus intermediate node, including its chosen anchor. -/
theorem plus_intermediate_node :
    InputCompositionCarrierCharts.chartNodes f g plus plus_projection 16 =
      InputCompositionCarrierBottom.nodes f g 7 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 16)
    (InputCompositionCarrierBottom.nodes f g 7) rfl (heq_of_eq (plus_intermediate_reference f g))

/-- The complete original plus target node, including its chosen anchor. -/
theorem plus_target_node :
    InputCompositionCarrierCharts.chartNodes f g plus plus_projection 17 =
      InputCompositionCarrierBottom.nodes f g 8 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 17)
    (InputCompositionCarrierBottom.nodes f g 8) rfl (heq_of_eq (plus_target_reference f g))

/-- The complete original minus source node, including its chosen anchor. -/
theorem minus_source_node :
    InputCompositionCarrierCharts.chartNodes f g minus minus_projection 15 =
      InputCompositionCarrierBottom.nodes f g 12 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 15)
    (InputCompositionCarrierBottom.nodes f g 12) rfl
      (heq_of_eq (InputCompositionBottomReferences.minus_source_reference f g))

/-- The complete original minus intermediate node, including its chosen anchor. -/
theorem minus_intermediate_node :
    InputCompositionCarrierCharts.chartNodes f g minus minus_projection 16 =
      InputCompositionCarrierBottom.nodes f g 13 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 16)
    (InputCompositionCarrierBottom.nodes f g 13) rfl (heq_of_eq (minus_intermediate_reference f g))

/-- The complete original minus target node, including its chosen anchor. -/
theorem minus_target_node :
    InputCompositionCarrierCharts.chartNodes f g minus minus_projection 17 =
      InputCompositionCarrierBottom.nodes f g 14 := by
  exact full_node_eq
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 17)
    (InputCompositionCarrierBottom.nodes f g 14) rfl (heq_of_eq (minus_target_reference f g))

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomNodes
