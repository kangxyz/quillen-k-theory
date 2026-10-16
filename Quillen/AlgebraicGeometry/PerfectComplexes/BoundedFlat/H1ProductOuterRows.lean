/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1FirstOuterRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeMergedRightRows

/-! Whole product-cell outer rows matched to the original composition chart by full endpoints. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1References


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
open BassH0Merge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The projection at `a` followed by the normalized polynomial coefficient map along `u`. -/
abbrev outerProductPre := BassOverlap.projectionMap P (a := a) ≫
  normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The reference for the product's outer chart row at polynomial normalization node 2. -/
def outerProductReference := chartIso P u v α hb ≪≫
  isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u 2).2
    (CoefficientSquareFamilies.chartSource P v α).functor

/-- The original product row at the first polynomial normalization endpoint. -/
theorem product_outer_row (i : Fin 5) :
    BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (2, i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (outerProductPre P u)
      (outerProductReference P u v α hb) (CoefficientSquareFamilies.chartNodes P v α i) :=
  product_row_nodes (BassOverlap.commonReference P u v)
    (CoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
    (CoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).2) (chartIso P u v α hb) 2 i

/-- The first actual binary row in the product's outer edge. -/
theorem product_outer_first_representation : ∃ ρ, ∀ i : Fin 3,
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (2, NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) := by
  refine ⟨outerProductReference P u v α hb, fun i ↦ ?_⟩
  exact (product_outer_row P u v α hb _).trans (pre_square_first_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
    (BassOverlap.commonReference P u v) (outerProductPre P u) _ i)

/-- The other product binary row retains its actual chart source equality. -/
theorem product_outer_second_representation : ∃ ρ, ∀ i : Fin 3,
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (2, NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) := by
  refine ⟨outerProductReference P u v α hb ≪≫ isoWhiskerLeft (outerProductPre P u).functor
    (NativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
      (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)), fun i ↦
        ?_⟩
  exact (product_outer_row P u v α hb _).trans (pre_square_second_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
    (BassOverlap.commonReference P u v) (outerProductPre P u) _ i)

/-- The old middle-right row retains its original reference under both fixed precompositions. -/
theorem old_product_middle_representation : ∃ ρ, ∀ i : Fin 3,
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) := by
  refine ⟨BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (rightRowReference (BassOverlap.chartReference P u v α)
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u))
        (oldMiddleTripleReference P u v α)), fun i ↦ ?_⟩
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (merged_middle_right_row
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm i)
  exact hn.trans (pre_pre_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a))
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (CoefficientSquareFamilies.chartSource P v α) _
    (BassOverlap.commonToChartReference P u v α hc) _)

/-- The old first-right row uses the exact first-triple reference under those same maps. -/
theorem old_product_first_representation : ∃ ρ, ∀ i : Fin 3,
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (outerProductPre P u) ρ
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) := by
  refine ⟨BassOverlap.commonToChartReference P u v α hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (rightRowReference (BassOverlap.chartReference P u v α)
        (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
        (coefficientMap P ((polynomialUnderFunctor R).map u)) (Iso.refl _)), fun i ↦ ?_⟩
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (merged_first_right_row
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm i)
  exact hn.trans (pre_pre_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a))
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v))) _
    (BassOverlap.commonToChartReference P u v α hc) _)

include ha

/-- The already proved internal and first-half joins identify this entire shared endpoint node. -/
theorem product_old_outer_endpoint : BassH1References.chartNodes P u v α hb 12 =
    BassOverlap.chartOverlapNodes P u v α hc 13 :=
  (first_product_polynomial_first_nodes P u v α ha hb 2).symm.trans
    (first_old_outer_second_nodes P u v α ha hc 2)

/-- Full-node endpoint cancellation fixes the complete first product row. -/
theorem product_old_outer_first_nodes (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (2, NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) := by
  obtain ⟨ρ, hρ⟩ := product_outer_first_representation P u v α hb
  obtain ⟨σ, hσ⟩ := old_product_middle_representation P u v α hc
  exact pre_families_match (BassOverlap.commonReference P u v) (outerProductPre P u)
    (CoefficientSquareFamilies.chartSource P v α)
    (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
    hρ hσ 2 (product_old_outer_endpoint P u v α ha hb hc) i

/-- The full outer center, with its literal product and old-chart indices. -/
theorem product_old_outer_center : BassH1References.chartNodes P u v α hb 10 =
    BassOverlap.chartOverlapNodes P u v α hc 9 :=
  product_old_outer_first_nodes P u v α ha hb hc 0

/-- The other complete product row retains the same proved full source node. -/
theorem product_old_outer_second_nodes (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (2, NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) := by
  obtain ⟨ρ, hρ⟩ := product_outer_second_representation P u v α hb
  obtain ⟨σ, hσ⟩ := old_product_first_representation P u v α hc
  exact pre_families_match (BassOverlap.commonReference P u v) (outerProductPre P u)
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (binaryNodes (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v))) hρ hσ
    0 (product_old_outer_center P u v α ha hb hc) i

end Quillen.PerfectComplexes.BassH1Join
