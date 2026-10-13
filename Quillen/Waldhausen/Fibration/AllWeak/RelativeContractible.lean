/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.AllWeak.CoproductCylinder
public import Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation

/-! # Contractibility of the actual identity-relative total S-model

Every object is acyclic in the all-weak coarse structure. The previously
proved original relative evaluation, with the genuine coproduct cylinder,
identifies this actual relative total with the contracted all-weak
S-realization. This establishes contractibility only; no double-S loop or
homotopy-fiber comparison is assumed or asserted.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Fibration.AllWeak
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The literal original relative evaluation is an equivalence for every W. -/
def relativeEvaluationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    |TheoremA.diagonalSSet (RelativeRows.relativeSRows (nested W))|
      (waldhausenStructure W).Delooping :=
  RelativeRows.coarseEvaluationHomotopyEquiv (nested W) (extensionAxiom W)
    (jointData W) (jointData_secondEndpointSection W)

@[simp] theorem relativeEvaluationHomotopyEquiv_toFun :
    (relativeEvaluationHomotopyEquiv W).toFun =
      (SSet.toTop.map (RelativeRows.coarseEvaluation (nested W) (extensionAxiom W))).hom :=
  RelativeRows.coarseEvaluationHomotopyEquiv_toFun _ _ _ _

/-- The actual identity-relative total is contractible, without any fibration input. -/
instance relativeTotal_contractible :
    ContractibleSpace |TheoremA.diagonalSSet (RelativeRows.relativeSRows (nested W))| :=
  (relativeEvaluationHomotopyEquiv W).contractibleSpace

/-- The prescribed forward equivalence preserves the original zero point. -/
@[simp] theorem relativeCoarseEvaluation_hom_basepoint :
    TopCat.Hom.hom (Y := (waldhausenStructure W).Delooping)
      (SSet.toTop.map (RelativeRows.coarseEvaluation (nested W) (extensionAxiom W)))
      (RelativeRows.totalBasepoint (nested W)) = (waldhausenStructure W).kBasepoint := by
  exact RelativeRows.coarseEvaluation_basepoint (nested W) (extensionAxiom W)


end Quillen.Waldhausen.Fibration.AllWeak
