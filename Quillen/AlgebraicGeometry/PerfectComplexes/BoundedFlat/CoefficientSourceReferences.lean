/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ChartLastReferences

/-! The two anchored source-node comparisons for the original chart/bottom merge. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The composite Laurent coefficient scheme map, applying the map for `v` before the map for
`u`. -/
abbrev laurentComposite := coefficientMap P ((laurentUnderFunctor R).map v) ≫
  coefficientMap P ((laurentUnderFunctor R).map u)
/-- The chart map at `c` followed by the polynomial coefficient scheme maps for `v` and `u`. -/
abbrev chartComposite (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :=
  coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
    coefficientMap P ((polynomialUnderFunctor R).map u)

/-- The two original naturality equations identify the actual chart's final geometric total. -/
theorem chart_equation (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :
    chartComposite P u v α = laurentComposite P u v ≫ coefficientMap P (α.app a) :=
  (DoubleSquareTrack.total_eq
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm).symm

/-- The chart source reference is precisely the original equality-transported left route. -/
theorem chart_source_reference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (BassOverlap.chartOverlapNodes P u v α hc 15).2 =
      smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
        (BassOverlap.chart_total P u v α hc).symm) ≪≫
          boundedFlatNormalizedPullbackCompIso (chartComposite P u v α) (polynomialProjection P a))
        ≪≫ isoWhiskerLeft (boundedFlatNormalizedPullback (polynomialProjection P a))
          (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation P u v α)) ≪≫
            boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
              (coefficientMap P (α.app a)))) := by
  have he : (BassOverlap.chartNodes P u v α 15).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation P u v α)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (coefficientMap P (α.app a))) :=
    last_source_reference _ _ _ _ _ _ _ _ _
  change BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (BassOverlap.chartNodes P u v α 15).2 = _
  rw [he]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassOverlap.chart_total P u v α hc).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (chartComposite P u v α)
          (polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙
      boundedFlatNormalizedPullback (polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_equation P u v α)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (coefficientMap P (α.app a)))) = _
  rw [smallIso_precomp, ← smallIso_trans]

/-- The native positive bottom source reference retains the actual binary normalization iso. -/
theorem bottom_plus_source_reference : (BassBottomCommonFamily.nodes P u v 42).2 =
    smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
      isoWhiskerRight
        (boundedFlatNormalizedPullbackCompIso (laurentPlus P a) (polynomialProjection P a))
        (boundedFlatNormalizedPullback (laurentComposite P u v))) := by
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BassProjectionPath.nodes P a 2).2.prod
        (Iso.refl (BassLaurentBottomFace.source P u v).functor)) = _
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (boundedFlatNormalizedPullbackCompIso
      (laurentPlus P a) (polynomialProjection P a)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurentComposite P u v) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- The native negative bottom reference retains the exact positive-to-negative source transport. -/
theorem bottom_minus_source_reference : (BassBottomCommonFamily.nodes P u v 48).2 =
    smallIso ((eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
      isoWhiskerRight
        (eqToIso (congrArg boundedFlatNormalizedPullback
          ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)) ≪≫
          boundedFlatNormalizedPullbackCompIso (laurentMinus P a) (polynomialProjection P a))
        (boundedFlatNormalizedPullback (laurentComposite P u v))) := by
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BassProjectionPath.nodes P a 4).2.prod
        (Iso.refl (BassLaurentBottomFace.source P u v).functor)) = _
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
  have he : BassProjectionPath.sourceIso P a = smallIso (eqToIso
      (congrArg boundedFlatNormalizedPullback
        ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm))) :=
    (smallIso_eqToIso _).symm
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    isoWhiskerRight (BassProjectionPath.sourceIso P a ≪≫
      smallIso (boundedFlatNormalizedPullbackCompIso
        (laurentMinus P a) (polynomialProjection P a)))
      (BassLaurentBottomFace.source P u v).functor = _
  rw [he, ← smallIso_trans]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
          (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurentMinus P a) (polynomialProjection P a)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurentComposite P u v) ⋙ AsSmall.up) = _
  rw [smallIso_postcomp, ← smallIso_trans]

/-- Full anchored reference equality for the positive source node. -/
theorem plus_source_reference : (BassBottomCommonFamily.nodes P u v 15).2 =
    (BassBottomCommonFamily.nodes P u v 42).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 15).2 = _
  rw [chart_source_reference, bottom_plus_source_reference]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc, laurentPlus] using
    anchored_factorizations_strict (laurentComposite P u v) (laurentPlus P a)
      (polynomialProjection P a) (chartComposite P u v (underToLaurent R))
      (laurentPlus P a ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chart_equation P u v (underToLaurent R)) rfl
      (BassOverlap.chart_total P u v (underToLaurent R) (laurentPlus_projection P c)).symm
      (BassBottomCommonFamily.bottom_total P u v).symm

/-- Full anchored reference equality for the inverse source node, including source transport. -/
theorem minus_source_reference : (BassBottomCommonFamily.nodes P u v 33).2 =
    (BassBottomCommonFamily.nodes P u v 48).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 15).2 = _
  rw [chart_source_reference, bottom_minus_source_reference]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc, laurentMinus] using
    anchored_factorizations_strict (laurentComposite P u v) (laurentMinus P a)
      (polynomialProjection P a) (chartComposite P u v (underToLaurentInvert R))
      (laurentPlus P a ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chart_equation P u v (underToLaurentInvert R))
      ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)
      (BassOverlap.chart_total P u v (underToLaurentInvert R) (laurentMinus_projection P c)).symm
      (BassBottomCommonFamily.bottom_total P u v).symm

end Quillen.PerfectComplexes.BassReferenceMerge
