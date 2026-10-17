/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputCentral
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentPlacement

/-! The frozen M bottom is the entire original fifteen-node Laurent product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct

/-- The literal old fifteen-node face of the frozen whole M family. -/
def bottomFace : ⦋14⦌ ⟶ ⦋139⦌ :=
  SimplexCategory.Hom.mk ⟨BassMWholeOrder.oldIndex ∘ BassH1Order.oldIndex ∘
    BassSupportOrder.bottomFace.toOrderHom, BassMWholeOrder.oldBottom_monotone⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Every original bottom node retains its complete old common-reference isomorphism. -/
theorem original_bottom_nodes (i : Fin 15) :
    BassMWhole.nodes P p q (bottomFace.toOrderHom i) =
      BassBottomCommonFamily.bottomNodes P p q i := by
  change BassMWhole.nodes P p q (BassMWholeOrder.oldIndex
    (BassH1Order.oldIndex (BassSupportOrder.oldIndex
      (BassReferenceMerge.bottomFace.toOrderHom i)))) = _
  rw [BassMWhole.old_nodes, BassH1Merged.old_nodes, BassH0Merged.old_nodes,
    BassReferenceMerge.bottom_nodes]
  change BassBottomCommonFamily.nodes P p q (Fin.natAdd 36 i) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_right]

/-- The complete original lower face keeps both independent scalar times. -/
theorem original_bottom_parameter (r t : I) :
    laurentCube P p q (r, (0, t)) =
      mapParameter (reanchor (referenceIso P p q))
        (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q)
          (BassBottomCommonFamily.bottomNodes P p q)
          (BassLaurentBottomFace.parameter.{u} (r, t))) := by
  change mapParameter (reanchor (referenceIso P p q))
    (CommonReferenceNerve.parameter _ _ (BassMWhole.scalarCube.{u} ![r, 0, t])) = _
  rw [BassMWhole.cube_bottom]
  change mapParameter _ (CommonReferenceNerve.parameter _ _
    (StdSimplex.map BassMWholeOrder.oldIndex (StdSimplex.map BassH1Order.oldIndex
      (StdSimplex.map BassSupportOrder.oldIndex
        (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom
          (BassLaurentBottomFace.parameter.{u} (r, t))))))) = _
  simp only [← StdSimplex.map_comp]
  change mapParameter _ (CommonReferenceNerve.parameter _ _
    (StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter.{u} (r, t)))) = _
  rw [CommonReferenceNerve.parameter_face]
  exact congrArg (fun ns ↦ mapParameter (reanchor (referenceIso P p q))
    (CommonReferenceNerve.parameter (BassOverlap.commonReference P p q) ns
      (BassLaurentBottomFace.parameter.{u} (r, t)))) (funext (original_bottom_nodes P p q))

private theorem laurent_node (j : Fin 3) :
    (⟨BassLaurentBottomFace.vertices P p q j, BassLaurentBottomFace.references P p q j⟩ :
      Node (CoefficientBassLaurentCompositionCarrier.reference P p q)) =
      CoefficientBassLaurentCompositionCarrier.nodes P p q j := by
  fin_cases j <;> rfl

/-- The complete old product grid agrees with the anchored full-node composition grid. -/
theorem bottom_product_node (i : Fin 15) :
    reanchor (referenceIso P p q) (BassBottomCommonFamily.bottomNodes P p q i) =
      node (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
        (BassProjectionPath.source P a) (CoefficientBassLaurentCompositionCarrier.reference P p q)
        (InputLaurentProduct.pairAnchor P p q)
        (BassProjectionPath.nodes P a ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).1)
        (CoefficientBassLaurentCompositionCarrier.nodes P p q
          ((Quillen.SimplexGrid.indexEquiv 4 2).symm i).2) := by
  rw [← laurent_node]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [reanchor, node, BassBottomCommonFamily.bottomNodes,
    CommonReferenceProduct.references, InputLaurentProduct.pairAnchor, Iso.trans_assoc]

/-- The entire frozen M bottom is the original Bass path times the original Laurent binary path. -/
theorem bottom_product_parameter (r t : I) :
    laurentCube P p q (r, (0, t)) =
      FiniteParameter.parameter (BassProjectionPath.source P a)
        (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
        (fun N j ↦ node _ (BassProjectionPath.source P a)
          (CoefficientBassLaurentCompositionCarrier.reference P p q)
          (InputLaurentProduct.pairAnchor P p q) N
          (CoefficientBassLaurentCompositionCarrier.nodes P p q j))
        (CommonReferenceNerve.parameter (BassProjectionPath.source P a)
          (BassProjectionPath.nodes P a) (BassProjectionPath.parameter t),
          binaryPath (k := 2) 0 1 2 r) := by
  rw [original_bottom_parameter, mapParameter_parameter, FiniteParameter.parameter_characteristic]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q)) ns
      (Quillen.SimplexGrid.parameter 4 2
        (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 r)))
  funext i
  exact bottom_product_node P p q i

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputCentral
