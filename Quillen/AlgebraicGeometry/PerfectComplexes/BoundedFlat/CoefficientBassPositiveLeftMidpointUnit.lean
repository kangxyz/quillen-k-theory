/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftUnitReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PostReferenceFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed

/-!
# The whole original midpoint unit edge in the left route

The first new unit edge W_p postcomposed by Laurent q equals the middle old unit edge V_q
precomposed by coefficient p. Both endpoints are equal as full dependent reference nodes;
the whole edge then follows from its ordered two-node characteristic map at unchanged time.
No native cancellation, geometry replacement, or whole seed equality is assumed.
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
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftMidpointUnit
open BassH0Merge BassH1Join CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassPositiveJ0OuterBridge CoefficientBassPositiveJ0ShiftedBridge
open CoefficientBassPositiveLeftUnitReferences CoefficientBassPositiveC0CarrierSeed
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Exact first-component transport, retaining firstIso before right whiskering. -/
def firstTransport : Node (CoefficientLaurentUnitTenNodes.source P p) →
    Node (BassOverlap.commonReference P p q) :=
  postReferenceNode (BassOverlap.commonReference P p q)
    (BassH1Components.laurentMap P q) (BassH1References.firstIso P p q)

/-- Exact middle-component transport, retaining middleIso before left whiskering. -/
def middleTransport : Node (CoefficientLaurentUnitTenNodes.source P q) →
    Node (BassOverlap.commonReference P p q) :=
  preReferenceNode (BassOverlap.commonReference P p q)
    (BassH1Components.coefficientMapModel P p) (BassH1References.middleIso P p q)

/-- The lower endpoint is the original shared H1 central node, including its full reference. -/
theorem lower_node :
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 4) =
      middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 2) := by
  calc
    _ = firstTransport P p q (BassH0Diagram.nodes P p 26) :=
      congrArg (firstTransport P p q) (outer_nodes P p 4).symm
    _ = BassH1References.firstNodes P p q 26 := rfl
    _ = BassH1References.middleNodes P p q 2 := first_middle_center P p q
    _ = middleTransport P p q (BassH0Diagram.nodes P q 2) := rfl
    _ = _ := congrArg (middleTransport P p q) (outer_nodes P q 2)

/-- The actual first unit-reference equation transports every full input node. -/
theorem first_shift (N : Node (CoefficientLaurentUnitTenNodes.source P p)) :
    anchorNode (commonUnit P p q) (firstTransport P p q N) =
      firstTransport P p q (anchorNode (sourceUnit P p) N) := by
  change anchorNode _ (postReferenceNode _ _ _ N) = postReferenceNode _ _ _ (anchorNode _ N)
  rw [anchor_post_node, post_anchor_node, first_unit_reference]

/-- The actual middle unit-reference equation transports every full input node. -/
theorem middle_shift (N : Node (CoefficientLaurentUnitTenNodes.source P q)) :
    anchorNode (commonUnit P p q) (middleTransport P p q N) =
      middleTransport P p q (anchorNode (sourceUnit P q) N) := by
  change anchorNode _ (preReferenceNode _ _ _ N) = preReferenceNode _ _ _ (anchorNode _ N)
  rw [BassMOuterJoin.anchor_pre_node, pre_anchor_node, middle_unit_reference]

/-- The upper endpoint retains the actual two source units and the specified commonUnit. -/
theorem upper_node :
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 9) =
      middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 7) := by
  calc
    _ = firstTransport P p q (anchorNode (sourceUnit P p)
        (CoefficientLaurentUnitTenNodes.nodes P p 4)) :=
      congrArg (firstTransport P p q) (five_shift P p 4).symm
    _ = anchorNode (commonUnit P p q)
        (firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 4)) :=
      (first_shift P p q _).symm
    _ = anchorNode (commonUnit P p q)
        (middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 2)) :=
      congrArg (anchorNode (commonUnit P p q)) (lower_node P p q)
    _ = middleTransport P p q (anchorNode (sourceUnit P q)
        (CoefficientLaurentUnitTenNodes.nodes P q 2)) := middle_shift P p q _
    _ = _ := congrArg (middleTransport P p q) (five_shift P q 2)

/-- The complete original new p unit edge, transported at its original parameter. -/
def firstEdge : C(I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (mapParameter (firstTransport P p q)).comp
    ((parameter (CoefficientLaurentUnitTenNodes.source P p)
      (CoefficientLaurentUnitTenNodes.nodes P p)).comp
      CoefficientLaurentUnitTenNodes.W.toContinuousMap)

/-- The complete original old q unit edge, transported at the same original parameter. -/
def middleEdge : C(I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (mapParameter (middleTransport P p q)).comp
    ((parameter (CoefficientLaurentUnitTenNodes.source P q)
      (CoefficientLaurentUnitTenNodes.nodes P q)).comp
      CoefficientLaurentUnitTenNodes.V.toContinuousMap)

private def newUnitFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![4, 9], by decide⟩
private def oldUnitFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 7], by decide⟩

/-- Both full nodes identify every point on W_p and V_q, without changing their clocks. -/
theorem edge_parameter (s : I) : firstEdge P p q s = middleEdge P p q s := by
  change mapParameter _ (parameter _ _ (CoefficientLaurentUnitTenNodes.W s)) =
    mapParameter _ (parameter _ _ (CoefficientLaurentUnitTenNodes.V s))
  rw [mapParameter_parameter, mapParameter_parameter]
  have hW := map_edge newUnitFace 0 1 s
  have hV := map_edge oldUnitFace 0 1 s
  change StdSimplex.map newUnitFace.toOrderHom ((edge (0 : Fin 2) 1) s) =
    CoefficientLaurentUnitTenNodes.W s at hW
  change StdSimplex.map oldUnitFace.toOrderHom ((edge (0 : Fin 2) 1) s) =
    CoefficientLaurentUnitTenNodes.V s at hV
  rw [← hW, ← hV, parameter_face, parameter_face]
  apply congrArg (fun N : Fin 2 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N ((edge (0 : Fin 2) 1) s))
  funext i
  fin_cases i
  · exact lower_node P p q
  · exact upper_node P p q

/-- Equality of the entire continuous original unit-edge maps, before native evaluation. -/
theorem edge_eq : firstEdge P p q = middleEdge P p q := by
  ext s
  exact edge_parameter P p q s

/-- The same whole unit seam in the actual two-tip carrier's Laurent stratum. -/
theorem carrier_edge (s : I) :
    includeLaurent P p q (firstEdge P p q s) =
      includeLaurent P p q (middleEdge P p q s) :=
  congrArg (includeLaurent P p q) (edge_parameter P p q s)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftMidpointUnit
