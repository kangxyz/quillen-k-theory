/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionTree
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanMReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeOverlap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeFaces

/-!
# The exact full-reference first stage of the original M seam

Only the three old polynomial rectangle supports and eight old middle product supports are
transported through the original whole-family index. The two charts retain their separate
anchors and the middle keeps both independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open CommonReferenceNerve
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => coefficientReference P p q
local notation "F" => BassProjectionPath.WholeReference.reference P c E
local notation "η" => BassMWholeConeCarrier.referenceIso P p q

/-- The full first chart region restricts along its three original ordered rectangles. -/
theorem whole_vertex_plus_parameter (r t : I) :
    BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, lower t)) =
      mapParameter (CommonReferenceProduct.reanchor η)
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.movingNodes P p q (underToLaurent R) (laurentPlus_projection P c))
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, t))) := by
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (BassMVertexOrder.parameter.{u} (r, lower t)))) = _
  rw [BassMVertexOrder.parameter_plus]
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (StdSimplex.map BassMVertexOrder.plusIndex
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, t))))) = _
  rw [← StdSimplex.map_comp]
  apply congrArg (mapParameter (CommonReferenceProduct.reanchor η))
  obtain ⟨i, z, hz⟩ := BassMPrimitiveSupport.moving_support (r, t)
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported _ _ _
    (BassMWholeOrder.vertexIndex ∘ BassMVertexOrder.plusIndex)
    (fun j ↦ (BassMWhole.vertex_nodes P p q _).trans (BassMVertex.plus_nodes P p q j))
    (BassPrimitiveSupport.rectangleFace i) (BassMWholeOrder.vertexPlus_monotone i) z

/-- Both complete middle coordinates restrict only along their eight original product supports. -/
theorem whole_vertex_middle_parameter (r t : I) :
    BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, upper (lower t))) =
      mapParameter (CommonReferenceProduct.reanchor η)
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.middleNodes P p q) (BassMComponents.middleParameter.{u} (r, t))) := by
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (BassMVertexOrder.parameter.{u} (r, upper (lower t))))) = _
  rw [BassMVertexOrder.parameter_middle]
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (StdSimplex.map BassMVertexOrder.middleIndex
          (BassMComponents.middleParameter.{u} (r, t))))) = _
  rw [← StdSimplex.map_comp]
  apply congrArg (mapParameter (CommonReferenceProduct.reanchor η))
  obtain ⟨i, j, z, hz⟩ := BassMPrimitiveSupport.middle_support.{u} r t
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported _ _ _
    (BassMWholeOrder.vertexIndex ∘ BassMVertexOrder.middleIndex)
    (fun k ↦ (BassMWhole.vertex_nodes P p q _).trans (BassMVertex.middle_nodes P p q k))
    (BassMPrimitiveSupport.middleEdgePairFace i j)
    (BassMWholeOrder.vertexMiddle_monotone i j) z

/-- The inverse chart keeps its separate reference and the original reversed path coordinate. -/
theorem whole_vertex_minus_parameter (r t : I) :
    BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, upper (upper t))) =
      mapParameter (CommonReferenceProduct.reanchor η)
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.movingNodes P p q
            (underToLaurentInvert R) (laurentMinus_projection P c))
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm t))) := by
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (BassMVertexOrder.parameter.{u} (r, upper (upper t))))) = _
  rw [BassMVertexOrder.parameter_minus]
  change mapParameter (CommonReferenceProduct.reanchor η)
    (CommonReferenceNerve.parameter _ (BassMWhole.nodes P p q)
      (StdSimplex.map BassMWholeOrder.vertexIndex
        (StdSimplex.map BassMVertexOrder.minusIndex
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm t))))) = _
  rw [← StdSimplex.map_comp]
  apply congrArg (mapParameter (CommonReferenceProduct.reanchor η))
  obtain ⟨i, z, hz⟩ := BassMPrimitiveSupport.moving_support (r, unitInterval.symm t)
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported _ _ _
    (BassMWholeOrder.vertexIndex ∘ BassMVertexOrder.minusIndex)
    (fun j ↦ (BassMWhole.vertex_nodes P p q _).trans (BassMVertex.minus_nodes P p q j))
    (BassPrimitiveSupport.rectangleFace i) (BassMWholeOrder.vertexMinus_monotone i) z

/-- The complete positive half is the original M chart region in the identical full reference. -/
theorem treeSquare_beta_lower (r t : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeSquare P p q (r, lower t)) =
      BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, lower t)) := by
  rw [treeSquare_lower, ← FourEdgeTree.realized_comp,
    BassProjectionPath.WholeReference.FourEdge.beta_plus]
  change mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c E
    (underToLaurent R) (laurentPlus_projection P c)) (polynomialSquare P p q (r, t)) = _
  exact (polynomialSquare_chart P p q (underToLaurent R) (laurentPlus_projection P c) r t).trans
    (whole_vertex_plus_parameter P p q r t).symm

/-- The middle quarter is the whole independent overlap family in its original grid reference. -/
theorem treeSquare_beta_middle (r t : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeSquare P p q (r, upper (lower t))) =
      BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, upper (lower t))) := by
  rw [treeSquare_middle, BassProjectionPath.WholeReference.FourEdge.beta_overlap]
  exact (middle_product_parameter P p q r t).symm.trans
    (whole_vertex_middle_parameter P p q r t).symm

/-- The final quarter retains the original inverse chart reversal and full moving reference. -/
theorem treeSquare_beta_upper (r t : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeSquare P p q (r, upper (upper t))) =
      BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, upper (upper t))) := by
  rw [treeSquare_upper, ← FourEdgeTree.realized_comp,
    BassProjectionPath.WholeReference.FourEdge.beta_minus]
  change mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c E
    (underToLaurentInvert R) (laurentMinus_projection P c))
      (polynomialSquare P p q (r, unitInterval.symm t)) = _
  exact (polynomialSquare_chart P p q (underToLaurentInvert R)
    (laurentMinus_projection P c) r (unitInterval.symm t)).trans
      (whole_vertex_minus_parameter P p q r t).symm

/-- Every first-stage value agrees in the full Laurent nerve with the unchanged selected M face. -/
theorem treeSquare_beta (r t : I) :
    SSet.toTop.map (BassProjectionPath.WholeReference.FourEdge.beta P c E)
        (treeSquare P p q (r, t)) =
      BassMWholeConeCarrier.parameter P p q
        (BassMScalarPasting.vertex.{u} BassMWholeOrder.vertexIndex (r, t)) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · exact treeSquare_beta_lower P p q r s
  · exact treeSquare_beta_middle P p q r s
  · exact treeSquare_beta_upper P p q r s

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
