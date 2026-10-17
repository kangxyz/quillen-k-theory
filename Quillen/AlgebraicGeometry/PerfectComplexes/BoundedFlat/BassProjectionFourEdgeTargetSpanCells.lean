/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanDescent
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluationCells

/-! The six complete original cells of the coefficient span lift, with unchanged global clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)

theorem treeMap_second (y : |FourEdgeTree.second E Ja|) :
    treeMap P f E (SSet.toTop.map (secondInTree E Ja) y) = secondValue P f E y := by
  rw [secondInTree, realized_comp, treeMap_third, thirdValue_second]

theorem treeMap_first (y : |FourEdgeTree.first E Ja|) :
    treeMap P f E (SSet.toTop.map (firstInTree E Ja) y) = firstValue P f E y := by
  rw [firstInTree, realized_comp, treeMap_second, secondValue_first]

/-- The entire genuine positive polynomial input is sent by the original coefficient map. -/
theorem treeMap_plus (y : |parameterSSet (E ≫ Ja)|) :
    treeMap P f E (SSet.toTop.map (plusVertex E Ja) y) = plusMap P f E y := by
  rw [plusVertex, realized_comp, treeMap_first, firstValue_plus]

/-- The first quarter is the first reversed half of the polynomial square. -/
theorem treeMap_edge12 (y : |parameterSSet E|) (t : I) :
    treeMap P f E (realizedEdge (edge12 E Ja) (y, t)) =
      plusSquare P f E (y, lower (unitInterval.symm t)) := by
  rw [edge12, realizedEdge_comp]
  change treeMap P f E (SSet.toTop.map (firstInTree E Ja)
    (DoubleCylinder.realizedCylinder (𝟙 _) (attachment E Ja) (y, ULift.up t))) = _
  rw [treeMap_first]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (𝟙 _) (attachment E Ja))
    (oneValue P f E) (plusMap P f E) (firstHomotopy P f E) t y

/-- The second quarter finishes the reversed positive polynomial square. -/
theorem treeMap_edge01 (y : |parameterSSet E|) (t : I) :
    treeMap P f E (realizedEdge (edge01 E Ja) (y, t)) =
      plusSquare P f E (y, unitInterval.symm (lower t)) := by
  rw [edge01, realizedEdge_comp]
  change treeMap P f E (SSet.toTop.map (secondInTree E Ja)
    (DoubleCylinder.realizedCylinder (𝟙 _) (firstOne E Ja) (y, ULift.up t))) = _
  rw [treeMap_second]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (𝟙 _) (firstOne E Ja))
    (zeroValue P f E) (firstValue P f E) (secondHomotopy P f E) t y

/-- The third quarter traverses the whole target overlap, without an added pause. -/
theorem treeMap_edge03 (y : |parameterSSet E|) (t : I) :
    treeMap P f E (realizedEdge (edge03 E Ja) (y, t)) = central P f E (y, t) := by
  rw [edge03, realizedEdge_comp]
  change treeMap P f E (SSet.toTop.map (thirdInTree E Ja)
    (DoubleCylinder.realizedCylinder (secondZero E Ja) (𝟙 _) (y, ULift.up t))) = _
  rw [treeMap_third]
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (secondZero E Ja) (𝟙 _))
    (secondValue P f E) (threeValue P f E) (thirdHomotopy P f E) t y

/-- The final quarter is the entire negative polynomial square in reverse. -/
theorem treeMap_edge34 (y : |parameterSSet E|) (t : I) :
    treeMap P f E (realizedEdge (edge34 E Ja) (y, t)) =
      minusSquare P f E (y, unitInterval.symm t) := by
  change treeMap P f E
    (DoubleCylinder.realizedCylinder (thirdThree E Ja) (attachment E Ja) (y, ULift.up t)) = _
  exact DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (DoubleCylinder.realized_isPushout (thirdThree E Ja) (attachment E Ja))
    (thirdValue P f E) (minusMap P f E) (fourthHomotopy P f E) t y

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
