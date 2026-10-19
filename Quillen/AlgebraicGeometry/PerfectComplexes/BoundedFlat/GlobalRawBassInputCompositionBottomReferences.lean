/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierBottom
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ChartLastReferences

/-!
# Original bottom/chart source anchors for global input composition

The two original geometric factorizations identify the full references at the positive and
inverse chart source nodes. The negative source transport remains the actual equality between
the two projection composites. Only generic normalized-pullback associativity is reused.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes.BassReferenceMerge
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomReferences
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The unchanged eighteen original rectangle nodes before polynomial precomposition. -/
abbrev rawChartNodes (k : laurent ⟶ polynomial) :=
  DoubleSquareMergedSimplex.nodes
    (polynomial.map g) (polynomial.map f) (laurent.map g) (laurent.map f)
    (k.app Z) (k.app Y) (k.app X) (k.naturality g).symm (k.naturality f).symm

/-- The actual composite of the two original Laurent scheme maps. -/
abbrev laurentComposite := laurent.map f ≫
  laurent.map g
/-- The original chart followed by the two actual polynomial scheme maps. -/
abbrev chartComposite (k : laurent ⟶ polynomial) :=
  k.app X ≫ polynomial.map f ≫
    polynomial.map g

/-- The two original naturality equations identify the actual chart's final geometric total. -/
theorem chart_equation (k : laurent ⟶ polynomial) :
    chartComposite f g k = laurentComposite f g ≫ k.app Z :=
  (DoubleSquareTrack.total_eq
    (polynomial.map g)
    (polynomial.map f)
    (laurent.map g)
    (laurent.map f)
    (k.app Z) (k.app Y) (k.app X)
    (k.naturality g).symm
    (k.naturality f).symm).symm

/-- The chart source reference is precisely the original equality-transported left route. -/
theorem chart_source_reference (k : laurent ⟶ polynomial)
    (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V) :
    (InputCompositionCarrierCharts.chartNodes f g k hk 15).2 =
      smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
        (InputCompositionCarrierCharts.chart_total f g k hk).symm) ≪≫
          boundedFlatNormalizedPullbackCompIso (chartComposite f g k) (projection.app Z))
        ≪≫ isoWhiskerLeft (boundedFlatNormalizedPullback (projection.app Z))
          (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation f g k)) ≪≫
            boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
              (k.app Z))) := by
  have he : (rawChartNodes f g k 15).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation f g k)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (k.app Z)) :=
    last_source_reference _ _ _ _ _ _ _ _ _
  change InputCompositionCarrierCharts.chartReferenceIso f g k hk ≪≫
    isoWhiskerLeft (InputCompositionCarrierCharts.projectionMap (Z := Z)).functor
      (rawChartNodes f g k 15).2 = _
  rw [he]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (InputCompositionCarrierCharts.chart_total f g k hk).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (chartComposite f g k)
          (projection.app Z)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙
      boundedFlatNormalizedPullback (projection.app Z) ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation f g k)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (k.app Z))) = _
  rw [smallIso_precomp, ← smallIso_trans]

/-- The native positive bottom source reference retains the actual binary normalization iso. -/
theorem bottom_plus_source_reference : (InputCompositionCarrierBottom.nodes f g 6).2 =
    smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
      (InputCompositionCarrierBottom.total f g).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (plus.app Z ≫ projection.app Z)) ≪≫
      isoWhiskerRight
        (boundedFlatNormalizedPullbackCompIso (plus.app Z) (projection.app Z))
        (boundedFlatNormalizedPullback (laurentComposite f g))) := by
  change InputCompositionCarrierBottom.sourceIso f g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((InputIdentityProjection.nodes Z 2).2.prod
        (Iso.refl (InputCompositionCarrierBottom.laurentSource f g).functor)) = _
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (InputCompositionCarrierBottom.total f g).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (plus.app Z ≫ projection.app Z)) ≪≫
    isoWhiskerRight (smallIso (boundedFlatNormalizedPullbackCompIso
      (plus.app Z) (projection.app Z)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurentComposite f g) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- The native negative bottom reference retains the exact positive-to-negative source transport. -/
theorem bottom_minus_source_reference : (InputCompositionCarrierBottom.nodes f g 12).2 =
    smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
      (InputCompositionCarrierBottom.total f g).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (plus.app Z ≫ projection.app Z)) ≪≫
      isoWhiskerRight
        (eqToIso (congrArg boundedFlatNormalizedPullback
          ((plus_projection Z).trans (minus_projection Z).symm)) ≪≫
          boundedFlatNormalizedPullbackCompIso (minus.app Z) (projection.app Z))
        (boundedFlatNormalizedPullback (laurentComposite f g))) := by
  change InputCompositionCarrierBottom.sourceIso f g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((InputIdentityProjection.nodes Z 4).2.prod
        (Iso.refl (InputCompositionCarrierBottom.laurentSource f g).functor)) = _
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
  have he : InputIdentityProjection.sourceIso Z = smallIso (eqToIso
      (congrArg boundedFlatNormalizedPullback
        ((plus_projection Z).trans (minus_projection Z).symm))) :=
    (smallIso_eqToIso _).symm
  change InputCompositionCarrierBottom.sourceIso f g ≪≫
    isoWhiskerRight (InputIdentityProjection.sourceIso Z ≪≫
      smallIso (boundedFlatNormalizedPullbackCompIso
        (minus.app Z) (projection.app Z)))
      (InputCompositionCarrierBottom.laurentSource f g).functor = _
  rw [he, ← smallIso_trans]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (InputCompositionCarrierBottom.total f g).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite f g)
          (plus.app Z ≫ projection.app Z)) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      ((plus_projection Z).trans (minus_projection Z).symm)) ≪≫
        boundedFlatNormalizedPullbackCompIso (minus.app Z) (projection.app Z)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurentComposite f g) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- Full anchored reference equality for the positive source node. -/
theorem plus_source_reference :
    (InputCompositionCarrierCharts.chartNodes f g plus plus_projection 15).2 =
    (InputCompositionCarrierBottom.nodes f g 6).2 := by
  rw [chart_source_reference, bottom_plus_source_reference]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    anchored_factorizations_strict (laurentComposite f g) (plus.app Z)
      (projection.app Z) (chartComposite f g plus)
      (plus.app Z ≫ projection.app Z)
      (laurent.map (f ≫ g) ≫ laurentProjection.app Z)
      (chart_equation f g plus) rfl
      (InputCompositionCarrierCharts.chart_total f g plus plus_projection).symm
      (InputCompositionCarrierBottom.total f g).symm

/-- Full anchored reference equality for the inverse source node, including source transport. -/
theorem minus_source_reference :
    (InputCompositionCarrierCharts.chartNodes f g minus minus_projection 15).2 =
    (InputCompositionCarrierBottom.nodes f g 12).2 := by
  rw [chart_source_reference, bottom_minus_source_reference]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    anchored_factorizations_strict (laurentComposite f g) (minus.app Z)
      (projection.app Z) (chartComposite f g minus)
      (plus.app Z ≫ projection.app Z)
      (laurent.map (f ≫ g) ≫ laurentProjection.app Z)
      (chart_equation f g minus)
      ((plus_projection Z).trans (minus_projection Z).symm)
      (InputCompositionCarrierCharts.chart_total f g minus minus_projection).symm
      (InputCompositionCarrierBottom.total f g).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionBottomReferences
