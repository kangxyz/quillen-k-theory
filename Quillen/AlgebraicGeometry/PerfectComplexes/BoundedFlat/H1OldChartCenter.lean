/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OldChartMiddleNormal

/-! Full original first-component/chart centers in their actual shared reference. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH1References
open Quillen.PerfectComplexes.BassReferenceMerge


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/--
The first-component outer chart center, normalized at the polynomial projection and postcomposed
by the Laurent map along `v`.
-/
def firstOuterCenter : BassOverlap.Node P u v :=
  postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a),
      eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)⟩ : BassH0Diagram.Node P u)

/--
The old outer chart center, normalized at the Laurent map along `v` and precomposed by the
projection at `a`.
-/
def oldOuterCenter : BassOverlap.Node P u v :=
  BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)),
      eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))⟩ :
      Σ G, (BassOverlap.chartReference P u v α).functor ≅ G.functor)

theorem first_outer_center_original :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha 9) = firstOuterCenter P u v α ha :=
  congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v)) (chart_middle_right_normal P u α ha)

theorem old_outer_center_original : BassOverlap.chartOverlapNodes P u v α hc 5 =
    oldOuterCenter P u v α hc :=
  congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (old_chart_middle_normal P u v α)

theorem outer_center_functor : (firstOuterCenter P u v α ha).1.functor =
    (oldOuterCenter P u v α hc).1.functor := rfl

/-- All original chart, projection and composition equality transports agree canonically. -/
theorem outer_center_reference : (firstOuterCenter P u v α ha).2 =
    (oldOuterCenter P u v α hc).2 := by
  have hfirst : eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartMiddleRightGeom P u α ha)) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  have hold : eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (oldChartMiddleGeom P u v α)) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)) (BassH1Components.laurentMap P v).functor =
    BassOverlap.commonToChartReference P u v α hc ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (eqToIso (oldChartMiddleSourceEq P u v α) ≪≫ BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u)))
  rw [hfirst, hold]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (first_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartMiddleRightGeom P u α ha)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
          (polynomialProjection P a)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassOverlap.chart_total P u v α hc).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback (polynomialProjection P a) ⋙
      AsSmall.up)
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (oldChartMiddleGeom P u v α)) ≪≫
        boundedFlatNormalizedPullbackCompIso (coefficientMap P ((laurentUnderFunctor R).map v))
          (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    (anchored_factorizations_strict (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a)
      (coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (oldChartMiddleGeom P u v α) (chartMiddleRightGeom P u α ha)
      (BassOverlap.chart_total P u v α hc).symm (first_total P u v).symm).symm

/-- The actual full outer center is shared with the unchanged old composition chart. -/
theorem first_old_chart_center :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha 9) =
      BassOverlap.chartOverlapNodes P u v α hc 5 := by
  rw [first_outer_center_original, old_outer_center_original]
  apply Sigma.ext (Model.Hom.ext (outer_center_functor P u v α ha hc))
  exact heq_of_eq (outer_center_reference P u v α ha hc)

/-- Full positive first-cell/chart center in the fixed old44 family. -/
theorem first_old_plus_center : BassH1References.firstNodes P u v 9 =
    BassReferenceMerge.nodes P u v 5 :=
  (first_old_chart_center P u v (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P c)).trans
    (BassH0Merge.old_plus_node P u v 5).symm

/-- Full inverse first-cell/chart center, with its distinct inverse-coordinate reference. -/
theorem first_old_minus_center : BassH1References.firstNodes P u v 20 =
    BassReferenceMerge.nodes P u v 29 :=
  (first_old_chart_center P u v (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P c)).trans
    (BassH0Merge.old_minus_node P u v 5).symm

end Quillen.PerfectComplexes.BassH1Join
