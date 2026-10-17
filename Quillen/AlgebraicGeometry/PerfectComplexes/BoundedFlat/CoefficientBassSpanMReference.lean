/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeReference

/-!
# The two polynomial moving regions retain the original M references

The cone reference is the inverse of the original middle-product anchor. The existing
anchored factorization identity then identifies both complete eighteen-node moving families,
including the separate positive and inverse chart anchors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open BassReferenceMerge BassH0Merge CommonReferenceNerve Quillen.SimplexParameters
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => coefficientReference P p q
local notation "F" => BassProjectionPath.WholeReference.reference P c E

/-- The full cone reference is precisely the inverse original middle-product normalization. -/
theorem cone_reference_middle : BassMWholeConeCarrier.referenceIso P p q =
    (BassMReferences.middleIso P p q).symm := by
  unfold BassMWholeConeCarrier.referenceIso
    CoefficientBassSeedCarrierLaurentReference.referenceIso BassMReferences.middleIso
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- All fifteen original product nodes become the literal whole-input finite-family grid. -/
theorem middle_product_nodes (i : Fin 15) :
    CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q)
        (BassMReferences.middleNodes P p q i) =
      FiniteParameter.gridNodes E F (BassProjectionPath.WholeReference.nodes P c E)
        (coefficientNodes P p q) i := by
  simp only [CommonReferenceProduct.reanchor, BassMReferences.middleNodes,
    BassH1Join.reanchoredProductNode, cone_reference_middle, Iso.symm_self_id_assoc]; rfl

/-- Both independent middle times agree in the full Laurent reference nerve. -/
theorem middle_product_parameter (r t : I) :
    mapParameter (CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q))
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.middleNodes P p q) (BassMComponents.middleParameter.{u} (r, t))) =
      BassProjectionPath.WholeReference.family P c E (coefficientPath P p q r, t) := by
  change mapParameter _ (CommonReferenceNerve.parameter _ _ _) =
    BassProjectionPath.WholeReference.family P c E
      (CommonReferenceNerve.parameter E (coefficientNodes P p q) (binaryPath 0 1 2 r), t)
  rw [BassProjectionPath.WholeReference.family_characteristic, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter F N
    (Quillen.SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath 0 1 2 r, BassProjectionPath.parameter t)))
  funext i
  exact middle_product_nodes P p q i

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The actual chart attachment and the original moving anchor agree before any evaluation. -/
theorem moving_chart_anchor :
    BassMWholeConeCarrier.referenceIso P p q ≪≫ BassMReferences.movingIso P p q α hc =
      isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso (c := c) P α hc) ≪≫
        isoWhiskerRight (squareAnchor P p q)
          (normalizedMap (coefficientMap P (α.app c))).functor := by
  let T := isoWhiskerRight
    (BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P q ≫ coefficientMap P p))
    (normalizedMap (coefficientMap P (α.app c))).functor
  let L := isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso (c := c) P α hc)
  have h : BassMReferences.movingIso P p q α hc ≪≫ T =
      BassMReferences.middleIso P p q ≪≫ L := BassMJoin.internal_reference P p q α hc
  calc
    _ = (BassMWholeConeCarrier.referenceIso P p q ≪≫
        (BassMReferences.movingIso P p q α hc ≪≫ T)) ≪≫ T.symm := by
      simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = (BassMWholeConeCarrier.referenceIso P p q ≪≫
        (BassMReferences.middleIso P p q ≪≫ L)) ≪≫ T.symm := by rw [h]
    _ = L ≪≫ T.symm := by rw [cone_reference_middle, Iso.symm_self_id_assoc]
    _ = _ := rfl

/-- Every complete original moving node is the chart attachment of its polynomial-source node. -/
theorem moving_chart_nodes (i : Fin 18) :
    BassProjectionPath.WholeReference.chartAttachmentNode P c E α hc (squareNodes P p q i) =
      CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q)
        (BassMReferences.movingNodes P p q α hc i) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso (c := c) P α hc) ≪≫
      isoWhiskerRight (squareAnchor P p q ≪≫ (originalNodes P p q i).2)
        (normalizedMap (coefficientMap P (α.app c))).functor =
    BassMWholeConeCarrier.referenceIso P p q ≪≫
      (BassMReferences.movingIso P p q α hc ≪≫
        isoWhiskerRight (originalNodes P p q i).2
          (normalizedMap (coefficientMap P (α.app c))).functor)
  rw [isoWhiskerRight_trans, ← Iso.trans_assoc, ← moving_chart_anchor, Iso.trans_assoc]

/-- The full eighteen-node characteristic map retains the actual original moving reference. -/
theorem moving_chart_parameter (z : StdSimplex ℝ (Fin 18)) :
    mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c E α hc)
        (CommonReferenceNerve.parameter (polynomialReference P p q) (squareNodes P p q) z) =
      mapParameter (CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q))
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.movingNodes P p q α hc) z) := by
  rw [mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter F N z)
  funext i
  exact moving_chart_nodes P p q α hc i

/-- Every point of the moving polynomial square has the unchanged charted M parameter. -/
theorem polynomialSquare_chart (r s : I) :
    mapParameter (BassProjectionPath.WholeReference.chartAttachmentNode P c E α hc)
        (polynomialSquare P p q (r, s)) =
      mapParameter (CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q))
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassMReferences.movingNodes P p q α hc)
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s))) :=
  moving_chart_parameter P p q α hc _

/-- Every positive polynomial node is retained at its actual position in the fixed whole M cube. -/
theorem moving_plus_whole_nodes (i : Fin 18) :
    BassProjectionPath.WholeReference.chartAttachmentNode P c E
        (underToLaurent R) (laurentPlus_projection P c) (squareNodes P p q i) =
      CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q)
        (BassMWhole.nodes P p q
          (BassMWholeOrder.vertexIndex (BassMVertexOrder.plusIndex i))) := by
  rw [BassMWhole.vertex_nodes, BassMVertex.plus_nodes]
  exact moving_chart_nodes P p q (underToLaurent R) (laurentPlus_projection P c) i

/-- The inverse polynomial nodes keep their separate chart and unchanged whole-cube positions. -/
theorem moving_minus_whole_nodes (i : Fin 18) :
    BassProjectionPath.WholeReference.chartAttachmentNode P c E
        (underToLaurentInvert R) (laurentMinus_projection P c) (squareNodes P p q i) =
      CommonReferenceProduct.reanchor (BassMWholeConeCarrier.referenceIso P p q)
        (BassMWhole.nodes P p q
          (BassMWholeOrder.vertexIndex (BassMVertexOrder.minusIndex i))) := by
  rw [BassMWhole.vertex_nodes, BassMVertex.minus_nodes]
  exact moving_chart_nodes P p q (underToLaurentInvert R) (laurentMinus_projection P c) i

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
