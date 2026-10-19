/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopVertex
public import Quillen.Aglib.Topology.Path.CarrierHalfPaths
public import Quillen.Aglib.Topology.Path.SpanReassociation
public import Quillen.Topology.Path.ScalarPathCells

/-!
# The exact original five-path top word of global input composition

The top positive and inverse moving paths are split at their literal half clocks. Together
with the original middle product they recover the entire vertex-stage top. The prescribed
three-stage five-piece reassociation is then retained without replacing any original leaf.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells Quillen.ScalarRectangle
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopWord
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
open InputCompositionTopPieces

/-- The entire positive top path, anchored at the proved original middle endpoint. -/
def plusTop : Path (movingFace f g plus plus_projection (1, 0))
    (middleFace f g (1, 0)) where
  toFun s := movingFace f g plus plus_projection (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := InputCompositionTopVertex.plus_middle f g 1

/-- The distinct inverse top path retains its own original projection endpoint. -/
def minusTop : Path (movingFace f g minus minus_projection (1, 0))
    (middleFace f g (1, 1)) where
  toFun s := movingFace f g minus minus_projection (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := InputCompositionTopVertex.minus_middle f g 1

/-- The entire original middle top path between the two actual projection endpoints. -/
def overlapTop : Path (middleFace f g (1, 0)) (middleFace f g (1, 1)) where
  toFun s := middleFace f g (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual first half of a path, preserving its specified source endpoint. -/
def firstHalf {T : Type*} [TopologicalSpace T] {a b : T} (p : Path a b) :
    Path a (p Path.CarrierHalfPaths.middle) :=
  (Path.CarrierHalfPaths.first p.toContinuousMap).cast p.source.symm rfl

/-- The actual final half of a path, preserving its specified target endpoint. -/
def lastHalf {T : Type*} [TopologicalSpace T] {a b : T} (p : Path a b) :
    Path (p Path.CarrierHalfPaths.middle) b :=
  (Path.CarrierHalfPaths.last p.toContinuousMap).cast rfl p.target.symm

private theorem first_last {T : Type*} [TopologicalSpace T] {a b : T} (p : Path a b) :
    (firstHalf p).trans (lastHalf p) = p := by
  apply Path.ext
  funext s
  exact Path.CarrierHalfPaths.trans_apply p.toContinuousMap s

/-- The first original positive square leaf. -/
def firstPlus := firstHalf (plusTop f g)
/-- The second original positive square leaf. -/
def lastPlus := lastHalf (plusTop f g)
/-- The first original inverse square leaf before its reversal. -/
def firstMinus := firstHalf (minusTop f g)
/-- The second original inverse square leaf before its reversal. -/
def lastMinus := lastHalf (minusTop f g)

/-- The literal target association of the five original span-cylinder leaves. -/
def pastedTop := ((firstPlus f g).trans (lastPlus f g)).trans
  ((overlapTop f g).trans ((lastMinus f g).symm.trans (firstMinus f g).symm))

/-- The complete five-leaf target word is the unchanged whole vertex-stage top. -/
theorem pastedTop_apply (s : unitInterval) :
    pastedTop f g s = InputCompositionTopVertex.face f g (1, s) := by
  change (((firstHalf (plusTop f g)).trans (lastHalf (plusTop f g))).trans
    ((overlapTop f g).trans
      ((lastHalf (minusTop f g)).symm.trans (firstHalf (minusTop f g)).symm))) s = _
  rw [first_last, ← Path.trans_symm, first_last]
  rcases three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [path_lower, InputCompositionTopVertex.face_plus]
    rfl
  · rw [path_upper, path_lower, InputCompositionTopVertex.face_middle]
    rfl
  · rw [path_upper, path_upper, InputCompositionTopVertex.face_minus]
    rfl

/-- The literal actual-composite association of those same five unchanged leaves. -/
def actualTop := (firstPlus f g).trans
  (((lastPlus f g).trans ((overlapTop f g).trans (lastMinus f g).symm)).trans
    (firstMinus f g).symm)

/-- Exactly the original three-stage five-piece reassociation, with both native coordinates. -/
def reassociation : (actualTop f g).Homotopy (pastedTop f g) :=
  Path.Homotopy.spanReassociation (firstPlus f g) (lastPlus f g) (overlapTop f g)
    (lastMinus f g).symm (firstMinus f g).symm

/-- Reverse only the original reassociation coordinate for the second half of M. -/
def reverseReassociation :
    C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  ⟨fun z ↦ reassociation f g (unitInterval.symm z.1, z.2), by fun_prop⟩

/-- The initial whole boundary is the actual vertex top, including every overlap point. -/
theorem reverse_zero (s : unitInterval) :
    reverseReassociation f g (0, s) = InputCompositionTopVertex.face f g (1, s) := by
  change reassociation f g (unitInterval.symm 0, s) = _
  rw [unitInterval.symm_zero, ContinuousMap.HomotopyWith.apply_one]
  exact pastedTop_apply f g s

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopWord
