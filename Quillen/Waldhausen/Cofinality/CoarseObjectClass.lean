/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Cofinality.GradedKZero
public import Quillen.Waldhausen.GrothendieckComparison.ObjectCompatibility

/-!
# Original object classes under the coarse grading equivalence

The existing realized group-grade map sends the original object edge to its
actual range-valued grade arrow. The resulting K-zero formula retains both
the chosen basepoint and the original equivalence.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.Cofinality.Grading
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

/-- The unchanged coarse object simplex is the actual range-valued grade arrow. -/
@[simp] theorem groupGradeMap_objectSimplex (A : C) :
    (d.groupGradeMap T).app (op ⦋1⦌) (d.coarseStructure.kZeroObjectSimplex A) =
      ComposableArrows.mk₁ (SingleObj.toEnd (Multiplicative (d.valueRange T))
        (Multiplicative.ofAdd (d.valueToRange T A))) := by
  refine ComposableArrows.ext₁ (F := (d.groupGradeMap T).app (op ⦋1⦌)
    (d.coarseStructure.kZeroObjectSimplex A)) (G := _) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The literal realized object loop maps to its original grade arrow loop. -/
theorem groupGradeMap_objectLoop (A : C) :
    ((d.coarseStructure.kZeroObjectLoop A).map
      (SSet.toTop.map (d.groupGradeMap T)).hom.continuous).cast
        (d.groupGradeMap_basepoint T).symm (d.groupGradeMap_basepoint T).symm =
      classifyingSpacePath (SingleObj.toEnd (Multiplicative (d.valueRange T))
        (Multiplicative.ofAdd (d.valueToRange T A))) := by
  ext t
  change SSet.toTop.map (d.groupGradeMap T)
    (realizationEdgePath (d.coarseStructure.kZeroObjectEdge A) t) = _
  exact (realizationEdgePath_naturality_apply (d.groupGradeMap T)
    (d.coarseStructure.kZeroObjectEdge A) t).trans
      (congrArg (fun e : (nerve (SingleObj (Multiplicative (d.valueRange T)))) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t))
          (d.groupGradeMap_objectSimplex T A))

/-- The original coarse K-zero equivalence retains every original object class. -/
@[simp] theorem coarseKZeroEquiv_objectClass (A : C) :
    d.coarseKZeroEquiv T (d.coarseStructure.kZeroObjectClass A) =
      Multiplicative.ofAdd (d.valueToRange T A) := by
  apply (GroupoidClassifying.singleObjPiOneEquiv _).injective
  change GroupoidClassifying.singleObjPiOneEquiv _
    ((GroupoidClassifying.singleObjPiOneEquiv _).symm
      (d.coarseKZeroToGroupPi T (d.coarseStructure.kZeroObjectClass A))) = _
  rw [MulEquiv.apply_symm_apply]
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (homotopyGroupMap (SSet.toTop.map (d.groupGradeMap T)).hom
      (d.groupGradeMap_basepoint T) (d.coarseStructure.kZeroObjectClass A)) = _
  rw [pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (d.coarseStructure.kZeroFundamentalGroupEquiv
      (d.coarseStructure.kZeroObjectClass A)) = _
  rw [d.coarseStructure.kZeroFundamentalGroupEquiv_objectClass,
    FundamentalGroup.mapOfEq_apply]
  simp only [GroupoidClassifying.singleObjPiOneEquiv_apply]
  exact congrArg Path.Homotopic.Quotient.mk (d.groupGradeMap_objectLoop T A)

end Quillen.Waldhausen.Cofinality.Grading
