/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductStrips
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0TypedUnitRails
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomPositiveColumn

/-! The two full source-unit references and the entire original direct-Laurent unit rail. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Simplicial Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldUnitSourceRail
open CommonReferenceNerve Quillen.SimplexParameters
open CoefficientBassPositiveC1SourceUnitProduct CoefficientBassPositiveC1SourceProductStrips
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The bottom source node retains the actual common-reference H0 anchor. -/
theorem start_node : positiveStartNodes P p q 0 = BassH0Merge.nodes P p q 2 := by
  rw [← positiveNine_start_nodes, positiveNine_bottom_nodes]
  exact (BassReferenceMerge.bottom_nodes P p q (SimplexGrid.index 4 2 (0, 0))).symm.trans
    (BassH0Merge.positive_source_nodes P p q 0).symm

/-- The original two endpoints of V, in their original order. -/
def oldUnitFace : ⦋1⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![2, 7], by decide⟩

/-- Both full product-column nodes are the anchored V2 and V7 nodes. -/
theorem source_nodes (i : Fin 2) :
    unitSixNodes P p q (SimplexGrid.index 1 2 (i, 0)) =
      BassH0Merge.anchorNode
        (eqToIso (BassH0Merge.reference_eq P p q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) (oldUnitFace.toOrderHom i)) := by
  fin_cases i
  · change unitSixNodes P p q (0 : Fin 6) =
      BassH0Merge.anchorNode (eqToIso (BassH0Merge.reference_eq P p q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) 2)
    have h := unitSix_lower_nodes P p q (0 : Fin 3)
    change unitSixNodes P p q (0 : Fin 6) = positiveStartNodes P p q 0 at h
    rw [h, start_node]
    exact congrArg
      (BassH0Merge.anchorNode
        (eqToIso (BassH0Merge.reference_eq P p q)))
      (CoefficientBassPositiveJ0OuterBridge.outer_nodes P (p ≫ q) 2)
  · change unitSixNodes P p q (3 : Fin 6) =
      BassH0Merge.anchorNode (eqToIso (BassH0Merge.reference_eq P p q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q) 7)
    have h := unitSix_upper_nodes P p q (0 : Fin 3)
    change unitSixNodes P p q (3 : Fin 6) =
      CommonReferenceProduct.reanchor (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (positiveStartNodes P p q 0) at h
    rw [h, start_node]
    exact CoefficientBassPositiveJ0ShiftedBridge.anchored_five_shift P p q (p ≫ q)
      (eqToIso (BassH0Merge.reference_eq P p q)) 2

/-- The entire source edge uses the unchanged edge clock, before any native evaluation. -/
theorem source_parameter (s : I) :
    unitParameter P p q (0, s) =
      mapParameter (BassH0Merge.anchorNode
        (eqToIso (BassH0Merge.reference_eq P p q)))
        (parameter (CoefficientLaurentUnitTenNodes.source P (p ≫ q))
          (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q))
          (CoefficientLaurentUnitTenNodes.V s)) := by
  rw [unit_source, mapParameter_parameter]
  rw [show CoefficientLaurentUnitTenNodes.V s =
    StdSimplex.map oldUnitFace.toOrderHom (edge (k := 1) 0 1 s) from
      (map_edge oldUnitFace 0 1 s).symm]
  rw [parameter_face]
  exact congrArg (fun N ↦ parameter (BassOverlap.commonReference P p q) N
    (edge (k := 1) 0 1 s)) (funext (source_nodes P p q))

variable (d : Under R)
open CoefficientBassPositiveJ0ConeBoundaries CoefficientBassPositiveJ0Rectangles

/-- Original actual source cast and both unit endpoint references, for the whole carrier rail. -/
theorem actual_old_unit (s : I) :
    CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
      (unitParameter P (firstArrow d) (secondArrow d) (0, s)) =
        CoefficientBassPositiveJ0TypedUnitRails.oldUnit P d s := by
  rw [source_parameter]
  change CoefficientBassPositiveJ0RectangleRails.unitMap P d
    (CoefficientLaurentUnitTenNodes.V s) = _
  rw [CoefficientBassPositiveJ0DirectUnit.unitMap_direct]; rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldUnitSourceRail
