/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointUnit

/-!
# Exact midpoint seed equality in the original two-tip carrier

The complete first-new and middle-old nulls are joined to their actual W_p and V_q unit
edges. Their full endpoint references license the original nested seed words. L3's whole
null/time equations and L4's whole unchanged-clock unit edge give equality of these paths,
without reassociation, native cancellation, or an assumed external seed equation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftMidpointSeed
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveLeftCellParameters CoefficientBassPositiveLeftConeSquares
open CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveJ0OuterBridge CoefficientBassPositiveJ0ShiftedBridge
open LaurentUnitReferenceSpecialization

private theorem parameter_vertex {V W : Model.{v}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) = nodePoint F (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) = StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The first new-positive source, retaining its ordinary or commonUnit-shifted reference. -/
def firstStart (e : Bool) : Carrier P p q :=
  includeLaurent P p q (parameter (laurentReference P p q)
    (firstRectangleNodes P p q e)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace 0))

/-- The middle old-positive source, retaining the corresponding full reference. -/
def middleStart (e : Bool) : Carrier P p q :=
  includeLaurent P p q (parameter (laurentReference P p q)
    (middleRectangleNodes P p q e)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace 0))

/-- The original first new null is exactly K.trans A(1), on each separate sheet. -/
def firstFullNull (e : Bool) : Path (firstStart P p q e) (tip P p q e) :=
  (firstNewPositive P p q e).trans (APath P p q e 1)

/-- The original middle old null is exactly D.trans (L.trans cylinder(Q(0))). -/
def middleFullNull (e : Bool) : Path (middleStart P p q e) (tip P p q e) :=
  (middleOldPositive P p q e).trans (middleNull P p q e)

/-- Full first endpoint reference, before identifying any carrier or native value. -/
theorem first_lower_reference : BassH1References.firstNodes P p q 26 =
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 4) :=
  congrArg (firstTransport P p q) (outer_nodes P p 4)

/-- Full middle endpoint reference, using its original precomposition anchor. -/
theorem middle_lower_reference : BassH1References.middleNodes P p q 2 =
    middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 2) :=
  congrArg (middleTransport P p q) (outer_nodes P q 2)

/-- The shifted first start is precisely the actual upper W_p node after transport. -/
theorem first_upper_reference :
    anchorNode (commonUnit P p q)
      (firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 4)) =
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 9) :=
  (first_shift P p q _).trans
    (congrArg (firstTransport P p q) (five_shift P p 4))

/-- The shifted middle start is precisely the actual upper V_q node after transport. -/
theorem middle_upper_reference :
    anchorNode (commonUnit P p q)
      (middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 2)) =
    middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 7) :=
  (middle_shift P p q _).trans
    (congrArg (middleTransport P p q) (five_shift P q 2))

/-- The first null source is the characteristic vertex of its complete transported node. -/
theorem first_start_node (e : Bool) : firstStart P p q e =
    includeLaurent P p q (nodePoint (laurentReference P p q)
      (sheetNode P p q e
        (firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 4)))) := by
  change includeLaurent P p q (parameter _ _
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace 0)) = _
  rw [Path.source, parameter_vertex]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (congrArg (sheetNode P p q e) (first_lower_reference P p q))

/-- The middle null source is the characteristic vertex of its complete transported node. -/
theorem middle_start_node (e : Bool) : middleStart P p q e =
    includeLaurent P p q (nodePoint (laurentReference P p q)
      (sheetNode P p q e
        (middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 2)))) := by
  change includeLaurent P p q (parameter _ _
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace 0)) = _
  rw [Path.source, parameter_vertex]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (congrArg (sheetNode P p q e) (middle_lower_reference P p q))

/-- W_p starts at the entire ordinary first-null source, in the actual carrier. -/
theorem first_unit_source : includeLaurent P p q (firstEdge P p q 0) =
    firstStart P p q false := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.W 0))) = _
  rw [Path.source, mapParameter_parameter, parameter_vertex, first_start_node]; rfl

/-- W_p ends at the entire shifted first-null source, with the actual commonUnit. -/
theorem first_unit_target : includeLaurent P p q (firstEdge P p q 1) =
    firstStart P p q true := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.W 1))) = _
  rw [Path.target, mapParameter_parameter, parameter_vertex, first_start_node]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (first_upper_reference P p q).symm

/-- V_q starts at the entire ordinary middle-null source, in the actual carrier. -/
theorem middle_unit_source : includeLaurent P p q (middleEdge P p q 0) =
    middleStart P p q false := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.V 0))) = _
  rw [Path.source, mapParameter_parameter, parameter_vertex, middle_start_node]; rfl

/-- V_q ends at the entire shifted middle-null source, with the actual commonUnit. -/
theorem middle_unit_target : includeLaurent P p q (middleEdge P p q 1) =
    middleStart P p q true := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.V 1))) = _
  rw [Path.target, mapParameter_parameter, parameter_vertex, middle_start_node]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (middle_upper_reference P p q).symm

/-- The complete original W_p unit path, with no change to its unit coordinate. -/
def firstUnit : Path (firstStart P p q false) (firstStart P p q true) where
  toFun s := includeLaurent P p q (firstEdge P p q s)
  continuous_toFun := by fun_prop
  source' := first_unit_source P p q
  target' := first_unit_target P p q

/-- The complete original V_q unit path at the same unit coordinate. -/
def middleUnit : Path (middleStart P p q false) (middleStart P p q true) where
  toFun s := includeLaurent P p q (middleEdge P p q s)
  continuous_toFun := by fun_prop
  source' := middle_unit_source P p q
  target' := middle_unit_target P p q

/-- The first-new midpoint seed keeps its literal inverse-null, unit, forward-null nesting. -/
def firstNewSeed : Path (tip P p q false) (tip P p q true) :=
  (firstFullNull P p q false).symm.trans
    ((firstUnit P p q).trans (firstFullNull P p q true))

/-- The middle-old midpoint seed keeps precisely the same original outer nesting. -/
def middleOldSeed : Path (tip P p q false) (tip P p q true) :=
  (middleFullNull P p q false).symm.trans
    ((middleUnit P p q).trans (middleFullNull P p q true))

/-- Whole midpoint seed equality at each original seed time, entirely inside the carrier. -/
theorem midpoint_seed_parameter (s : I) :
    firstNewSeed P p q s = middleOldSeed P p q s :=
  map_trans_values id (firstFullNull P p q false).symm
    ((firstUnit P p q).trans (firstFullNull P p q true))
    (middleFullNull P p q false).symm
    ((middleUnit P p q).trans (middleFullNull P p q true))
    (fun t ↦ null_time_seam P p q false (unitInterval.symm t))
    (map_trans_values id (firstUnit P p q) (firstFullNull P p q true)
      (middleUnit P p q) (middleFullNull P p q true)
      (carrier_edge P p q) (null_time_seam P p q true)) s

/-- Equality of the complete typed midpoint seed paths between the distinct original tips. -/
theorem midpoint_seed : firstNewSeed P p q = middleOldSeed P p q := by
  ext s
  exact midpoint_seed_parameter P p q s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftMidpointSeed
