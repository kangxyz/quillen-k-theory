/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.Constant
public import Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation
public import Quillen.Topology.HomotopyFiber.Basic

/-! # The literal original total-tail fiber comparison

The original split inclusion has an exactly zero tail, by the genuine
oneChain/ordinal split-fiber formula. Its total map therefore lifts to the
actual homotopy fiber with the entire path literally constant at the
original double-S zero. No global fiber weak equivalence is claimed.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [SmallCategory C]

/-- The original all-zero vertex of the actual ordinary double S-construction. -/
def ordinaryTotalZeroVertex (W : Structure C) :
    (TheoremA.diagonalSSet (ordinarySRows W)) _⦋0⦌ :=
  zeroSimplex (QuotientRows.waldhausenStructure W ⦋0⦌).cof
    (QuotientRows.waldhausenStructure W ⦋0⦌).weq
    (QuotientRows.zero W ⦋0⦌) (QuotientRows.isZero W ⦋0⦌) (op ⦋0⦌)

/-- The point represented by that exact original double-S zero vertex. -/
def ordinaryTotalBasepoint (W : Structure C) :
    |TheoremA.diagonalSSet (ordinarySRows W)| :=
  realizationPoint (ordinaryTotalZeroVertex W)

variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original diagonal tail, realized without changing its model. -/
def totalTailMap : C(|TheoremA.diagonalSSet (relativeSRows N)|,
    |TheoremA.diagonalSSet (ordinarySRows (acyclicStructure N))|) :=
  (SSet.toTop.map (TheoremA.diagonalMap (tailSRows N))).hom

/-- The original split inclusion has the literal constant-zero total tail.
This descends from the genuine original oneChain/ordinal formula fiber_tail. -/
theorem totalFiberInclusion_tail :
    totalFiberInclusion N ≫ TheoremA.diagonalMap (tailSRows N) =
      SSet.const (ordinaryTotalZeroVertex (acyclicStructure N)) := by
  unfold totalFiberInclusion
  have hd : TheoremA.diagonalMap (fiberSRows N) ≫ TheoremA.diagonalMap (tailSRows N) =
      TheoremA.diagonalMap (fiberSRows N ≫ tailSRows N) := rfl
  rw [Category.assoc, hd, fiberSRows_tailSRows]
  ext n F : 4
  apply Subtype.ext
  rfl

/-- Every original total fiber point has the original double-S zero as tail. -/
@[simp] theorem totalTailMap_totalFiberInclusion (x : V.Delooping) :
    totalTailMap N (SSet.toTop.map (totalFiberInclusion N) x) =
      ordinaryTotalBasepoint (acyclicStructure N) := by
  change (SSet.toTop.map (totalFiberInclusion N) ≫
    SSet.toTop.map (TheoremA.diagonalMap (tailSRows N))) x = _
  rw [← Functor.map_comp, totalFiberInclusion_tail]
  exact realization_const_apply _ x

/-- The original relative chosen point maps to the actual double-S chosen point. -/
@[simp] theorem totalTailMap_basepoint :
    totalTailMap N (totalBasepoint N) = ordinaryTotalBasepoint (acyclicStructure N) := by
  rw [← totalFiberInclusion_basepoint N]
  exact totalTailMap_totalFiberInclusion N V.kBasepoint

/-- The actual original constant-path total-tail fiber comparison. -/
def totalTailFiberComparison : C(V.Delooping,
    HomotopyFiber (totalTailMap N) (ordinaryTotalBasepoint (acyclicStructure N))) where
  toFun x := HomotopyFiber.basepoint (totalTailMap N)
    (ordinaryTotalBasepoint (acyclicStructure N))
    (SSet.toTop.map (totalFiberInclusion N) x) (totalTailMap_totalFiberInclusion N x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (SSet.toTop.map (totalFiberInclusion N)).hom.continuous.prodMk continuous_const

/-- Projection retains the original total split inclusion exactly. -/
@[simp] theorem totalTailFiberComparison_source (x : V.Delooping) :
    (totalTailFiberComparison N x).1.1 = SSet.toTop.map (totalFiberInclusion N) x := rfl

/-- The complete original fiber path is literally constant, at every source point. -/
@[simp] theorem totalTailFiberComparison_path (x : V.Delooping) :
    (totalTailFiberComparison N x).1.2 =
      ContinuousMap.const unitInterval (ordinaryTotalBasepoint (acyclicStructure N)) := rfl

/-- The original based point is the original constant-path relative zero. -/
@[simp] theorem totalTailFiberComparison_basepoint :
    totalTailFiberComparison N V.kBasepoint =
      HomotopyFiber.basepoint (totalTailMap N) (ordinaryTotalBasepoint (acyclicStructure N))
        (totalBasepoint N) (totalTailMap_basepoint N) := by
  apply Subtype.ext
  apply Prod.ext
  · exact totalFiberInclusion_basepoint N
  · rfl

end Quillen.Waldhausen.Fibration.RelativeRows
