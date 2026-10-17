/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductStrips
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0Rectangles
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomPositiveColumn

/-! Both whole old-positive source rails from the actual full product-column references. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Simplicial
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldPositiveSourceRails
open CommonReferenceNerve CoefficientBassPositiveC1SourceProductStrips
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original old-positive binary row, without deleting its raw middle node. -/
def sourceFace : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![2, 3, 11], by decide⟩

/-- The entire product source column equals the original anchored H0 row as full nodes. -/
theorem source_nodes (i : Fin 3) :
    positiveNineNodes P p q (SimplexGrid.index 2 2 (i, 0)) =
      BassH0Merge.nodes P p q
        ((sourceFace ≫ BassH0Diagram.plusFace).toOrderHom i) := by
  rw [positiveNine_bottom_nodes]
  have hb : BassBottomCommonFamily.nodes P p q
      (BassBottomCommonFamily.bottomFace.toOrderHom
        (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) =
      BassBottomCommonFamily.bottomNodes P p q
        (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0)) := by
    change BassBottomCommonFamily.nodes P p q
      (Fin.natAdd 36 (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0) : Fin 15)) = _
    unfold BassBottomCommonFamily.nodes
    rw [Fin.addCases_right]
  have hf : (sourceFace ≫ BassH0Diagram.plusFace).toOrderHom i =
      BassH0Diagram.plusFace.toOrderHom (BassH0Merge.rectangleLeftIndex i) := by
    fin_cases i <;> rfl
  rw [hf]
  exact hb.symm.trans ((BassReferenceMerge.bottom_nodes P p q
    (SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))).symm.trans
      (BassH0Merge.positive_source_nodes P p q i).symm)

/-- The complete source binary path preserves both normalization half clocks. -/
theorem source_parameter (s : I) :
    positiveParameter P p q (0, s) =
      parameter (BassOverlap.commonReference P p q) (BassH0Merge.nodes P p q)
        (ProjectionRectangleParameters.D BassH0Diagram.plusFace s) := by
  rw [positive_source]
  rw [show ProjectionRectangleParameters.D BassH0Diagram.plusFace s =
    StdSimplex.map (sourceFace ≫ BassH0Diagram.plusFace).toOrderHom
      (binaryPath (k := 2) 0 1 2 s) from
    (map_binaryPath (sourceFace ≫ BassH0Diagram.plusFace) 0 1 2 s).symm]
  rw [parameter_face]
  exact congrArg (fun N ↦ parameter (BassOverlap.commonReference P p q) N
    (binaryPath (k := 2) 0 1 2 s)) (funext (source_nodes P p q))

variable (d : Under R)
open CoefficientBassPositiveJ0ConeBoundaries CoefficientBassPositiveJ0Rectangles

/-- The ordinary carrier rail is exactly the chosen old-positive path at every time. -/
theorem actual_source_minus (s : I) :
    CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
      (positiveParameter P (firstArrow d) (secondArrow d) (0, s)) =
        oldPositiveMinus P d s := by
  rw [source_parameter]; rfl

/-- The separate shifted rail applies the full common-unit action, with the same original clock. -/
theorem actual_source_plus (s : I) :
    CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
      (shiftedPositiveParameter P (firstArrow d) (secondArrow d) (0, s)) =
        oldPositivePlus P d s := by
  change CutOpenCarrier.laurentInclusion _ _ _ _ _
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P (firstArrow d) (secondArrow d)))
      (positiveParameter P (firstArrow d) (secondArrow d) (0, s))) = _
  rw [source_parameter]; rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldPositiveSourceRails
