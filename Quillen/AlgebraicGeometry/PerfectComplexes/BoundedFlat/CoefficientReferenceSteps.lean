/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSourceReferences

/-! Propagation of the two source reference equalities along their original transformations. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassReferenceMerge

private theorem pair_row_step {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {K : C ⥤ E}
    (a : K ≅ F₀ ⋙ G₀) (e : F₀ ≅ F₁) (f : G₀ ≅ G₁) :
    a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (a ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod (Iso.refl G₀))) ≪≫
        isoWhiskerLeft F₁ f := by
  rw [composition_pair_iso, composition_pair_iso, isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.trans_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The first Laurent normalization step whiskered by the projection triangle's target functor
for `g`. -/
abbrev firstStep (g : (space (op P, (laurentUnderFunctor R).obj a)) ⟶
    space (op P, (polynomialUnderFunctor R).obj a)) :=
  isoWhiskerLeft (BinaryNormalizationSimplex.targetMap g (polynomialProjection P a)).functor
    (BinaryNormalizationSimplex.first
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

/-- The total Laurent normalization comparison whiskered by the projection triangle's target
functor for `g`. -/
abbrev totalStep (g : (space (op P, (laurentUnderFunctor R).obj a)) ⟶
    space (op P, (polynomialUnderFunctor R).obj a)) :=
  isoWhiskerLeft (BinaryNormalizationSimplex.targetMap g (polynomialProjection P a)).functor
    (BinaryNormalizationSimplex.total
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

/-- The full chart intermediate reference follows the original first normalization component. -/
theorem chart_first_step (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (BassOverlap.chartOverlapNodes P u v α hc 16).2 =
      (BassOverlap.chartOverlapNodes P u v α hc 15).2 ≪≫
        firstStep P u v (coefficientMap P (α.app a)) := by
  have hs : (BassOverlap.chartNodes P u v α 16).2 =
      (BassOverlap.chartNodes P u v α 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback (coefficientMap P (α.app a)))
          (BinaryNormalizationSimplex.geometricIso
            (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))) :=
    last_intermediate_reference _ _ _ _ _ _ _ _ _
  change BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (BassOverlap.chartNodes P u v α 16).2 =
    (BassOverlap.commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (BassOverlap.chartNodes P u v α 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

/-- The full chart endpoint reference follows the original total normalized component. -/
theorem chart_total_step (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (BassOverlap.chartOverlapNodes P u v α hc 17).2 =
      (BassOverlap.chartOverlapNodes P u v α hc 15).2 ≪≫
        totalStep P u v (coefficientMap P (α.app a)) := by
  have hs : (BassOverlap.chartNodes P u v α 17).2 =
      (BassOverlap.chartNodes P u v α 15).2 ≪≫
        smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback (coefficientMap P (α.app a)))
          (boundedFlatNormalizedPullbackCompIso
            (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))) :=
    last_target_reference _ _ _ _ _ _ _ _ _
  change BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (BassOverlap.chartNodes P u v α 17).2 =
    (BassOverlap.commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (BassOverlap.chartNodes P u v α 15).2) ≪≫ _
  rw [hs, isoWhiskerLeft_trans, Iso.trans_assoc]
  congr 1

theorem bottom_plus_first_step : (BassBottomCommonFamily.nodes P u v 43).2 =
    (BassBottomCommonFamily.nodes P u v 42).2 ≪≫ firstStep P u v (laurentPlus P a) :=
  pair_row_step (BassBottomCommonFamily.referenceIso P u v)
    (BassProjectionPath.nodes P a 2).2
    (BinaryNormalizationSimplex.first
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

theorem bottom_plus_total_step : (BassBottomCommonFamily.nodes P u v 44).2 =
    (BassBottomCommonFamily.nodes P u v 42).2 ≪≫ totalStep P u v (laurentPlus P a) :=
  pair_row_step (BassBottomCommonFamily.referenceIso P u v)
    (BassProjectionPath.nodes P a 2).2
    (BinaryNormalizationSimplex.total
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

theorem bottom_minus_first_step : (BassBottomCommonFamily.nodes P u v 49).2 =
    (BassBottomCommonFamily.nodes P u v 48).2 ≪≫ firstStep P u v (laurentMinus P a) :=
  pair_row_step (BassBottomCommonFamily.referenceIso P u v)
    (BassProjectionPath.nodes P a 4).2
    (BinaryNormalizationSimplex.first
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

theorem bottom_minus_total_step : (BassBottomCommonFamily.nodes P u v 50).2 =
    (BassBottomCommonFamily.nodes P u v 48).2 ≪≫ totalStep P u v (laurentMinus P a) :=
  pair_row_step (BassBottomCommonFamily.referenceIso P u v)
    (BassProjectionPath.nodes P a 4).2
    (BinaryNormalizationSimplex.total
      (BassLaurentBottomFace.firstMap P v) (BassLaurentBottomFace.secondMap P u))

theorem plus_intermediate_reference : (BassBottomCommonFamily.nodes P u v 16).2 =
    (BassBottomCommonFamily.nodes P u v 43).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 16).2 = _
  rw [chart_first_step, bottom_plus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep P u v (laurentPlus P a)) (plus_source_reference P u v)

theorem plus_target_reference : (BassBottomCommonFamily.nodes P u v 17).2 =
    (BassBottomCommonFamily.nodes P u v 44).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) 17).2 = _
  rw [chart_total_step, bottom_plus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep P u v (laurentPlus P a)) (plus_source_reference P u v)

theorem minus_intermediate_reference : (BassBottomCommonFamily.nodes P u v 34).2 =
    (BassBottomCommonFamily.nodes P u v 49).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 16).2 = _
  rw [chart_first_step, bottom_minus_first_step]
  exact congrArg (fun e ↦ e ≪≫ firstStep P u v (laurentMinus P a)) (minus_source_reference P u v)

theorem minus_target_reference : (BassBottomCommonFamily.nodes P u v 35).2 =
    (BassBottomCommonFamily.nodes P u v 50).2 := by
  change (BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P c) 17).2 = _
  rw [chart_total_step, bottom_minus_total_step]
  exact congrArg (fun e ↦ e ≪≫ totalStep P u v (laurentMinus P a)) (minus_source_reference P u v)

end Quillen.PerfectComplexes.BassReferenceMerge
