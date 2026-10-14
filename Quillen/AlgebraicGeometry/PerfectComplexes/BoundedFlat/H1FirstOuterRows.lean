/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OldChartCenter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeMergedColumns

/-! Whole first-cell outer chart rows with both original whiskerings and references retained. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

abbrev outerFirstSource := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
abbrev outerFirstBinary := binaryNodes
  (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
abbrev outerSecondSource := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))
abbrev outerSecondBinary := binaryNodes
  (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The first row representation is constructed from the original projection reference. -/
theorem first_outer_first_representation : ∃ ρ, ∀ i : Fin 3,
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassH1Components.laurentMap P v) (outerFirstSource P u α) (outerFirstBinary P u α) ρ i := by
  refine ⟨firstIso P u v ≪≫ isoWhiskerRight
    (rightRowReference (BassH0Diagram.reference P u)
      (coefficientMap P ((laurentUnderFunctor R).map u)) (coefficientMap P (α.app a))
      (polynomialProjection P a)
      (nativeFirstReference (polynomialProjection P a) (coefficientMap P (α.app a))
        (coefficientMap P ((laurentUnderFunctor R).map u)) (laurentProjection P a) ha))
    (BassH1Components.laurentMap P v).functor, ?_⟩
  intro i
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (native_first_right_row (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
      (coefficientTransformation_naturality P α u) (laurentProjection P a) ha i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) _ (firstIso P u v) i)

/-- The second row representation retains the actual middle-square source transport. -/
theorem first_outer_second_representation : ∃ ρ, ∀ i : Fin 3,
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassH1Components.laurentMap P v) (outerSecondSource P u α)
      (outerSecondBinary P u α) ρ i := by
  refine ⟨firstIso P u v ≪≫ isoWhiskerRight
    (rightRowReference (BassH0Diagram.reference P u)
      (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a) (polynomialMiddleReference P u α ha))
    (BassH1Components.laurentMap P v).functor, ?_⟩
  intro i
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (native_middle_right_row (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
      (coefficientTransformation_naturality P α u) (laurentProjection P a) ha i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) _ (firstIso P u v) i)

abbrev oldLastTripleReference := DoubleSquareCommonSimplex.lastSourceIso
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientTransformation_naturality P α u).symm
  (coefficientTransformation_naturality P α v).symm

abbrev oldMiddleTripleReference := DoubleSquareCommonSimplex.middleSourceIso
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((laurentUnderFunctor R).map v))
  (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
  (coefficientTransformation_naturality P α v).symm

/-- The old last column uses the original geometric total-square reference before precomposition. -/
theorem old_outer_last_representation : ∃ ρ, ∀ i : Fin 3,
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassH1Components.laurentMap P v) (outerFirstSource P u α) (outerFirstBinary P u α) ρ i := by
  refine ⟨BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (oldLastTripleReference P u v α ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))), ?_⟩
  intro i
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (merged_last_column
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientTransformation_naturality P α u).symm
      (coefficientTransformation_naturality P α v).symm i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) _
    (BassOverlap.commonToChartReference P u v α hc) i)

/-- The old middle column retains the original v-square source transport before precomposition. -/
theorem old_outer_middle_representation : ∃ ρ, ∀ i : Fin 3,
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassH1Components.laurentMap P v) (outerSecondSource P u α)
      (outerSecondBinary P u α) ρ i := by
  refine ⟨BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (oldMiddleTripleReference P u v α ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))), ?_⟩
  intro i
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (merged_middle_column
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientTransformation_naturality P α u).symm
      (coefficientTransformation_naturality P α v).symm i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) _
    (BassOverlap.commonToChartReference P u v α hc) i)

/-- The entire first original u-square binary row agrees with the old last column. -/
theorem first_old_outer_first_nodes (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) := by
  obtain ⟨ρ, hρ⟩ := first_outer_first_representation P u v α ha
  obtain ⟨σ, hσ⟩ := old_outer_last_representation P u v α hc
  exact prePost_families_match (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerFirstSource P u α) (outerFirstBinary P u α) hρ hσ
    0 (first_old_chart_center P u v α ha hc) i

/-- The entire other original u-square row agrees through the same full shared source. -/
theorem first_old_outer_second_nodes (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) := by
  obtain ⟨ρ, hρ⟩ := first_outer_second_representation P u v α ha
  obtain ⟨σ, hσ⟩ := old_outer_middle_representation P u v α hc
  exact prePost_families_match (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassH1Components.laurentMap P v)
    (outerSecondSource P u α) (outerSecondBinary P u α) hρ hσ
    0 (first_old_chart_center P u v α ha hc) i

end Quillen.PerfectComplexes.BassH1Join
