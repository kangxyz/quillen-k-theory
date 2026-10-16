/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductRowCenter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionChartRows

/-! Both original chart rows on the product/middle joins of H1. -/
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
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/-- The coefficient map along `u` followed by the normalized polynomial projection at `b`. -/
abbrev chartJoinPre := BassH1Components.coefficientMapModel P u ≫
  normalizedMap (polynomialProjection P b)

/--
The middle-component reference for the first chart row, obtained by prewhiskering its native
projection reference.
-/
def middleFirstChartReference := middleIso P u v ≪≫
  isoWhiskerLeft (BassH1Components.coefficientMapModel P u).functor
    (rightRowReference (BassH0Diagram.reference P v)
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
      (polynomialProjection P b)
      (nativeFirstReference (polynomialProjection P b) (coefficientMap P (α.app b))
        (coefficientMap P ((laurentUnderFunctor R).map v)) (laurentProjection P b) hb))

/--
The middle-component reference for the second chart row, retaining the chart naturality
transport along `v`.
-/
def middleSecondChartReference := middleIso P u v ≪≫
  isoWhiskerLeft (BassH1Components.coefficientMapModel P u).functor
    (rightRowReference (BassH0Diagram.reference P v)
      (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P b)
      (nativeMiddleReference (polynomialProjection P b) (coefficientMap P (α.app b))
        (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
          (laurentProjection P b) hb))

/-- The common reference for the product chart row at the final polynomial-square node. -/
def productChartReference := chartIso P u v α hb ≪≫
  isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u 4).2
    (CoefficientSquareFamilies.chartSource P v α).functor

/-- The original first chart row inside the middle H0 component. -/
theorem middle_first_chart_row (i : Fin 3) :
    preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preReferenceNode (BassOverlap.commonReference P u v) (chartJoinPre P u)
      (H := CoefficientSquareFamilies.chartSource P v α)
      (middleFirstChartReference P u v α hb)
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v))
    (native_first_right_row (polynomialProjection P b) (coefficientMap P (α.app b))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
        (laurentProjection P b) hb i)
  exact hn.trans (pre_pre_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (normalizedMap (polynomialProjection P b))
    (CoefficientSquareFamilies.chartSource P v α) _ (middleIso P u v) _)

/-- The second middle-component chart row retains the actual chart naturality transport. -/
theorem middle_second_chart_row (i : Fin 3) :
    preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preReferenceNode (BassOverlap.commonReference P u v) (chartJoinPre P u)
      (H := BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)))
      (middleSecondChartReference P u v α hb)
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v))
    (native_middle_right_row (polynomialProjection P b) (coefficientMap P (α.app b))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
        (laurentProjection P b) hb i)
  exact hn.trans (pre_pre_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (normalizedMap (polynomialProjection P b))
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v))) _ (middleIso P u v) _)

/-- The whole actual product row uses the original chart square after its fixed precomposition. -/
theorem product_chart_row (i : Fin 5) :
    BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (4, i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (chartJoinPre P u)
      (productChartReference P u v α hb) (CoefficientSquareFamilies.chartNodes P v α i) :=
  product_row_nodes (BassOverlap.commonReference P u v)
    (CoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
    (CoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).2) (chartIso P u v α hb) 4 i

/-- First binary normalization row in the actual fixed product row. -/
theorem product_chart_first_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (4, NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (chartJoinPre P u)
      (productChartReference P u v α hb)
      (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P (α.app b)) i) :=
  (product_chart_row P u v α hb _).trans (pre_square_first_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
    (BassOverlap.commonReference P u v) (chartJoinPre P u) (productChartReference P u v α hb) i)

/-- The other binary normalization row includes its unchanged original chart source equality. -/
theorem product_chart_second_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (4, NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (chartJoinPre P u)
      (productChartReference P u v α hb ≪≫ isoWhiskerLeft (chartJoinPre P u).functor
        (NativeSquareFiveSimplex.sourceIso
          (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
          (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
          (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)))
      (binaryNodes (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v)) i) :=
  (product_chart_row P u v α hb _).trans (pre_square_second_nodes
    (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map v))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
    (BassOverlap.commonReference P u v) (chartJoinPre P u) (productChartReference P u v α hb) i)

/-- Every first-row node agrees through the proved original full center. -/
theorem middle_product_chart_first_nodes (i : Fin 3) :
    preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (4, NativeSquareFiveSimplex.firstFace.toOrderHom i)) :=
  pre_families_match (BassOverlap.commonReference P u v) (chartJoinPre P u)
    (CoefficientSquareFamilies.chartSource P v α)
    (binaryNodes (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
    (middle_first_chart_row P u v α hb) (product_chart_first_row P u v α hb)
    0 (middle_product_chart_center P u v α hb) i

/-- Every second-row node retains the actual source transport and the same shared center. -/
theorem middle_product_chart_second_nodes (i : Fin 3) :
    preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (4, NativeSquareFiveSimplex.secondFace.toOrderHom i)) :=
  pre_families_match (BassOverlap.commonReference P u v) (chartJoinPre P u)
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (binaryNodes (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (middle_second_chart_row P u v α hb) (product_chart_second_row P u v α hb)
    0 (middle_product_chart_center P u v α hb) i

end Quillen.PerfectComplexes.BassH1Join
