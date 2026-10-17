/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomCenter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace

/-!
# The exact terminal unit V_B of the left route

The original V_p edge, postcomposed by Laurent q with firstIso, equals the terminal
source-unit column of C1. Both complete reference nodes are identified before taking
their characteristic edge. The result is a whole carrier path at unchanged unit time;
no native cancellation or terminal whole-seed equality is used.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalUnit
open BassH0Merge BassH1Join CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveJ0OuterBridge CoefficientBassPositiveJ0ShiftedBridge
open CoefficientBassPositiveC1SourceUnitProduct CoefficientBassPositiveC1SourceProductStrips
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The source-unit lower row is the original full positive-start row of the bottom product. -/
theorem positive_start_bottom (j : Fin 3) :
    positiveStartNodes P p q j = BassBottomCommonFamily.bottomNodes P p q
      (Quillen.SimplexGrid.index 4 2 (0, j)) :=
  (positiveNine_start_nodes P p q j).symm.trans (positiveNine_bottom_nodes P p q 0 j)

/-- The ordinary V_p endpoint is the exact bottom target-center reference of C1. -/
theorem lower_start_node :
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 2) =
      positiveStartNodes P p q 2 := by
  calc
    _ = firstTransport P p q (BassH0Diagram.nodes P p 2) :=
      congrArg (firstTransport P p q) (outer_nodes P p 2).symm
    _ = BassH1References.firstNodes P p q 2 := rfl
    _ = BassBottomCommonFamily.bottomNodes P p q 2 := first_bottom_center P p q
    _ = positiveStartNodes P p q 2 := (positive_start_bottom P p q 2).symm

/-- The full lower terminal unit node, including the actual bottom reference isomorphism. -/
theorem lower_node :
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 2) =
      unitSixNodes P p q (Quillen.SimplexGrid.index 1 2 (0, 2)) :=
  (lower_start_node P p q).trans (unitSix_lower_nodes P p q 2).symm

/-- The upper endpoint uses L2's actual right-whiskered unit and the accepted Unit6 upper node. -/
theorem upper_node :
    firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 7) =
      unitSixNodes P p q (Quillen.SimplexGrid.index 1 2 (1, 2)) := by
  calc
    _ = firstTransport P p q (anchorNode (sourceUnit P p)
        (CoefficientLaurentUnitTenNodes.nodes P p 2)) :=
      congrArg (firstTransport P p q) (five_shift P p 2).symm
    _ = anchorNode (commonUnit P p q)
        (firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p 2)) :=
      (first_shift P p q _).symm
    _ = anchorNode (commonUnit P p q) (positiveStartNodes P p q 2) :=
      congrArg (anchorNode (commonUnit P p q)) (lower_start_node P p q)
    _ = _ := (unitSix_upper_nodes P p q 2).symm

/-- The entire original V_p edge with its exact firstIso/right-whiskering transport. -/
def firstOldEdge : C(I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (mapParameter (firstTransport P p q)).comp
    ((parameter (CoefficientLaurentUnitTenNodes.source P p)
      (CoefficientLaurentUnitTenNodes.nodes P p)).comp
      CoefficientLaurentUnitTenNodes.V.toContinuousMap)

private def oldUnitFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 7], by decide⟩

/-- Equality of every whole-nerve value at the same unit time s and C1 composition time 1. -/
theorem terminal_parameter (s : I) :
    firstOldEdge P p q s = unitParameter P p q (1, s) := by
  change mapParameter _ (parameter _ _ (CoefficientLaurentUnitTenNodes.V s)) = _
  rw [mapParameter_parameter, unit_target]
  have hV := map_edge oldUnitFace 0 1 s
  change StdSimplex.map oldUnitFace.toOrderHom ((edge (0 : Fin 2) 1) s) =
    CoefficientLaurentUnitTenNodes.V s at hV
  rw [← hV, parameter_face]
  apply congrArg (fun N : Fin 2 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N ((edge (0 : Fin 2) 1) s))
  funext i
  fin_cases i
  · exact lower_node P p q
  · exact upper_node P p q

/-- The whole transported V_p path is literally the unit branch of the C1 endpoint. -/
theorem terminal_carrier (s : I) :
    includeLaurent P p q (firstOldEdge P p q s) =
      CoefficientBassPositiveC1SeedFace.forwardUnit P p q (s, 1) :=
  congrArg (includeLaurent P p q) (terminal_parameter P p q s)

/-- V_B is the actual C1 forward-unit slice at composition time 1. -/
def VB : Path (CoefficientBassPositiveC1SeedFace.ordinaryStart P p q 1)
    (CoefficientBassPositiveC1SeedFace.shiftedStart P p q 1) where
  toFun s := CoefficientBassPositiveC1SeedFace.forwardUnit P p q (s, 1)
  continuous_toFun := by fun_prop
  source' := (CoefficientBassPositiveC1SeedFace.forwardUnit P p q).apply_zero 1
  target' := (CoefficientBassPositiveC1SeedFace.forwardUnit P p q).apply_one 1

/-- The original first-old unit path, with both endpoint joins proved by full reference data. -/
def firstOldUnit : Path (CoefficientBassPositiveC1SeedFace.ordinaryStart P p q 1)
    (CoefficientBassPositiveC1SeedFace.shiftedStart P p q 1) where
  toFun s := includeLaurent P p q (firstOldEdge P p q s)
  continuous_toFun := by fun_prop
  source' := (terminal_carrier P p q 0).trans
    ((CoefficientBassPositiveC1SeedFace.forwardUnit P p q).apply_zero 1)
  target' := (terminal_carrier P p q 1).trans
    ((CoefficientBassPositiveC1SeedFace.forwardUnit P p q).apply_one 1)

/-- Equality of the entire typed unit paths, without selecting a replacement path or clock. -/
theorem firstOldUnit_eq_VB : firstOldUnit P p q = VB P p q := by
  ext s
  exact terminal_carrier P p q s

/-- The original seed's middle-quarter embedding keeps exactly the forward unit time s. -/
theorem terminal_seed_unit_branch (s : I) :
    includeLaurent P p q (firstOldEdge P p q s) =
      CoefficientBassPositiveC1SeedFace.face P p q
        (1, Quillen.NativePathCells.upper (Quillen.NativePathCells.lower s)) :=
  (terminal_carrier P p q s).trans
    (CoefficientBassPositiveC1SeedFace.face_third P p q 1 s).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalUnit
