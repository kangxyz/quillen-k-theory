/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointUnit

/-! The complete q-new starting seed equals the original reversed-C0 source face. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftStartingSeed
open BassH0Merge CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierSeed
open CoefficientBassPositiveC0CarrierRails CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveLeftPolynomialParameters CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftConeSquares CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveJ0OuterBridge CoefficientBassPositiveJ0ShiftedBridge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The ordered three-node positive target of the actual middle rectangle. -/
def positiveFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ BassH0Diagram.plusFace.toOrderHom
    (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)), by decide⟩

/-- The three actual q-new nodes are precisely the full C0 target projection nodes. -/
theorem positive_nodes (e : Bool) (i : Fin 3) :
    middleRectangleNodes P p q e (positiveFace.toOrderHom i) =
      sheetNode P p q e (targetProjectionNodes P p q i) := rfl

/-- The original q-new positive row keeps its binary clock and middleIso reference. -/
def newPositiveParameter (e : Bool) :
    C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (middleRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace).toContinuousMap

/-- Whole full-reference characteristic-map equality, including both actual sheets. -/
theorem positive_parameter (e : Bool) (s : I) : newPositiveParameter P p q e s =
    mapParameter (sheetNode P p q e) (targetProjectionParameter P p q s) := by
  change parameter _ _ (ProjectionRectangleParameters.K BassH0Diagram.plusFace s) =
    mapParameter _ (parameter _ _ ((binaryPath (0 : Fin 3) 1 2) s))
  rw [mapParameter_parameter]
  have h := map_binaryPath positiveFace 0 1 2 s
  change StdSimplex.map positiveFace.toOrderHom ((binaryPath (0 : Fin 3) 1 2) s) =
    ProjectionRectangleParameters.K BassH0Diagram.plusFace s at h
  rw [← h, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N ((binaryPath (0 : Fin 3) 1 2) s))
    (funext (positive_nodes P p q e))

theorem ordinary_positive (s : I) :
    includeLaurent P p q (newPositiveParameter P p q false s) =
      projectionMinus P p q (s, 1) := by
  rw [target_projection, positive_parameter]
  change includeLaurent P p q (mapParameter _ (parameter _ _ _)) =
    includeLaurent P p q (parameter _ _ _)
  rw [mapParameter_parameter]; rfl

theorem shifted_positive (s : I) :
    includeLaurent P p q (newPositiveParameter P p q true s) =
      projectionPlus P p q (s, 1) := by
  rw [target_projection_shifted, positive_parameter]; rfl

/-- The initial point of the new positive path for `q` on the ordinary or shifted sheet. -/
def newStart (e : Bool) : Carrier P p q :=
  includeLaurent P p q (newPositiveParameter P p q e 0)

/-- The original q-new positive path joins the actual Q(1) cylinder attachment. -/
def newPositive (e : Bool) : Path (newStart P p q e)
    (includeLaurent P p q (secondMovement P p q e 1)) where
  toFun s := includeLaurent P p q (newPositiveParameter P p q e s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := by
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.K BassH0Diagram.plusFace 1)) =
      includeLaurent P p q (parameter _ _
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace 1))
    rw [Path.target, Path.target]

/-- The whole q-new null is K.trans cylinder(Q(1)), at the original two half clocks. -/
def newNull (e : Bool) : Path (newStart P p q e) (tip P p q e) :=
  (newPositive P p q e).trans (BPath P p q e 1)

/-- The lower W_q node is the actual middle raw26 reference, before evaluation. -/
theorem lower_reference : BassH1References.middleNodes P p q 26 =
    middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 4) :=
  congrArg (middleTransport P p q) (outer_nodes P q 4)

/-- The upper W_q node retains L2's proved left-whiskered unit intertwining. -/
theorem upper_reference :
    anchorNode (commonUnit P p q)
      (middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 4)) =
    middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 9) :=
  (middle_shift P p q _).trans
    (congrArg (middleTransport P p q) (five_shift P q 4))

private theorem parameter_vertex {k : ℕ} (N : Fin (k + 1) → Node (laurentReference P p q))
    (i : Fin (k + 1)) : parameter (laurentReference P p q) N (StdSimplex.single i) =
      nodePoint (laurentReference P p q) (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) = StdSimplex.single i := by
    rw [StdSimplex.map_single]; rfl
  rw [← hm, parameter_face]; rfl

theorem start_node (e : Bool) : newStart P p q e =
    includeLaurent P p q (nodePoint (laurentReference P p q)
      (sheetNode P p q e
        (middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q 4)))) := by
  change includeLaurent P p q (parameter _ _
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace 0)) = _
  rw [Path.source, parameter_vertex]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (congrArg (sheetNode P p q e) (lower_reference P p q))

/-- The entire original W_q edge, with actual coefficient-p precomposition. -/
def newUnitParameter : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (mapParameter (middleTransport P p q)).comp
    ((parameter (CoefficientLaurentUnitTenNodes.source P q)
      (CoefficientLaurentUnitTenNodes.nodes P q)).comp
      CoefficientLaurentUnitTenNodes.W.toContinuousMap)

theorem unit_source : includeLaurent P p q (newUnitParameter P p q 0) =
    newStart P p q false := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.W 0))) = _
  rw [Path.source, mapParameter_parameter, parameter_vertex, start_node]; rfl

theorem unit_target : includeLaurent P p q (newUnitParameter P p q 1) =
    newStart P p q true := by
  change includeLaurent P p q (mapParameter _
    (parameter _ _ (CoefficientLaurentUnitTenNodes.W 1))) = _
  rw [Path.target, mapParameter_parameter, parameter_vertex, start_node]
  exact congrArg (fun N ↦ includeLaurent P p q (nodePoint (laurentReference P p q) N))
    (upper_reference P p q).symm

/-- The forward Laurent-unit path for `q`, precomposed by `p`, between the two `newStart`
points. -/
def newUnit : Path (newStart P p q false) (newStart P p q true) where
  toFun s := includeLaurent P p q (newUnitParameter P p q s)
  continuous_toFun := by fun_prop
  source' := unit_source P p q
  target' := unit_target P p q

/-- The whole unit path is the accepted full-reference C0 target unit, at unchanged time. -/
theorem unit_carrier (s : I) : newUnit P p q s = forwardUnit P p q (s, 1) :=
  (CoefficientBassPositiveC0CarrierSeed.target_unit P p q s).symm

theorem ordinary_cylinder (s : I) : BPath P p q false 1 s =
    contractionMinus P p q (s, 1) := by
  change minusCylinder P p q (secondParameter P p q 1, s) = _
  rw [second_target_parameter]
  exact (target_contractions P p q s).1.symm

theorem shifted_cylinder (s : I) : BPath P p q true 1 s =
    contractionPlus P p q (s, 1) := by
  change plusCylinder P p q (secondParameter P p q 1, s) = _
  rw [second_target_parameter]
  exact (target_contractions P p q s).2.symm

theorem ordinary_null (s : I) : newNull P p q false s = nullMinus P p q (s, 1) := by
  change ((newPositive P p q false).trans (BPath P p q false 1)) s =
    ((projectionMinus P p q).trans (contractionMinus P p q)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ordinary_positive P p q _
  · exact ordinary_cylinder P p q _

theorem shifted_null (s : I) : newNull P p q true s = nullPlus P p q (s, 1) := by
  change ((newPositive P p q true).trans (BPath P p q true 1)) s =
    ((projectionPlus P p q).trans (contractionPlus P p q)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact shifted_positive P p q _
  · exact shifted_cylinder P p q _

/-- The actual left starting seed: q-new null inverse, original W_q, shifted q-new null. -/
def startingSeed : Path (minusTip P p q) (plusTip P p q) :=
  (newNull P p q false).symm.trans ((newUnit P p q).trans (newNull P p q true))

/-- Whole C0 starting seam in the carrier, preserving every original outer half clock. -/
theorem starting_seed_target (s : I) : startingSeed P p q s = face P p q (1, s) := by
  change ((newNull P p q false).symm.trans
    ((newUnit P p q).trans (newNull P p q true))) s =
      ((nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ordinary_null P p q (unitInterval.symm _)
  · rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact unit_carrier P p q _
    · exact shifted_null P p q _

/-- This is precisely the source of reversed C0, without reversing the seed coordinate. -/
theorem starting_seed_reversedC0 (s : I) : startingSeed P p q s =
    reversedFace P p q (0, s) :=
  (starting_seed_target P p q s).trans (reversedFace_source P p q s).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftStartingSeed
