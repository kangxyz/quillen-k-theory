/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductColumnCenter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareBinaryNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionPolynomialColumns

/-! Full polynomial rows on both first/product H1 joins, with their original reference isos. -/
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
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

abbrev polynomialJoinPost := normalizedMap (coefficientMap P (α.app b)) ≫
  BassH1Components.laurentMap P v

abbrev polynomialMiddleReference := nativeMiddleReference
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientTransformation_naturality P α u) (laurentProjection P a) ha

def firstPolynomialRowReference := firstIso P u v ≪≫ isoWhiskerRight
  (polynomialMiddleReference P u α ha ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P (α.app b))
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))
  (BassH1Components.laurentMap P v).functor

def secondPolynomialRowReference := firstIso P u v ≪≫ isoWhiskerRight
  (BassH1H0Boundary.lastReference P u α ha ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P (α.app b)) (polynomialProjection P b ≫ coefficientMap P u))
  (BassH1Components.laurentMap P v).functor

def productPolynomialReference := chartIso P u v α hb ≪≫
  isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))

/-- The first component's first polynomial row is its original two normalizations postcomposed. -/
theorem first_polynomial_row (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
      (firstPolynomialRowReference P u v α ha)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (native_middle_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
      (coefficientTransformation_naturality P α u) (laurentProjection P a) ha i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app b))) (BassH1Components.laurentMap P v)
    (CoefficientSquareFamilies.polynomialSource P u) _ (firstIso P u v) _)

/-- The other polynomial row retains the native last-triple equality transport. -/
theorem second_polynomial_row (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
      (secondPolynomialRowReference P u v α ha)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (native_last_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
      (coefficientTransformation_naturality P α u) (laurentProjection P a) ha i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app b))) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    _ (firstIso P u v) _)

/-- The product column is the original whole polynomial square after fixed postcomposition. -/
theorem product_polynomial_column (i : Fin 5) :
    BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (i, 2)) =
    postReferenceNode (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb) (CoefficientSquareFamilies.polynomialNodes P u i) :=
  product_column_nodes (BassOverlap.commonReference P u v)
    (CoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
    (CoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).2) (chartIso P u v α hb) i 2

/-- The first product-column row retains the first original polynomial binary reference. -/
theorem product_polynomial_first_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.firstFace.toOrderHom i, 2)) =
    postReferenceNode (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) :=
  (product_polynomial_column P u v α hb _).trans (post_square_first_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (productPolynomialReference P u v α hb) i)

/-- The second product-column row retains the actual polynomial naturality source equality. -/
theorem product_polynomial_second_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.secondFace.toOrderHom i, 2)) =
    postReferenceNode (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
      (productPolynomialReference P u v α hb ≪≫ isoWhiskerRight
        (NativeSquareFiveSimplex.sourceIso
          (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
          (polynomialProjection P b) (coefficientMap P u)
          (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u))
        (polynomialJoinPost P v α).functor)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) :=
  (product_polynomial_column P u v α hb _).trans (post_square_second_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (productPolynomialReference P u v α hb) i)

/-- The complete first binary row is fixed by the proved original central node identity. -/
theorem first_product_polynomial_first_nodes (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) =
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.firstFace.toOrderHom i, 2)) :=
  post_families_match (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (CoefficientSquareFamilies.polynomialSource P u)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a))
    (first_polynomial_row P u v α ha) (product_polynomial_first_row P u v α hb)
    0 (first_product_polynomial_center P u v α ha hb) i

/-- The complete second binary row retains the full source identity and source transport. -/
theorem first_product_polynomial_second_nodes (i : Fin 3) :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha
        (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) =
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.secondFace.toOrderHom i, 2)) :=
  post_families_match (BassOverlap.commonReference P u v) (polynomialJoinPost P v α)
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    (binaryNodes (polynomialProjection P b) (coefficientMap P u))
    (second_polynomial_row P u v α ha) (product_polynomial_second_row P u v α hb)
    0 (first_product_polynomial_center P u v α ha hb) i

end Quillen.PerfectComplexes.BassH1Join
