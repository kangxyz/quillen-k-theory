/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Approximation.WeakRows

/-!
# Initial flags and actual quotient rows have equivalent classifying spaces

Canonical cokernel completion and initial-flag restriction act on the
actual pointwise weak-equivalence categories. The unit and counit are
constructed from the actual quotient isomorphisms, naturally for arbitrary
weak-equivalence transformations, not only for diagram isomorphisms.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen

open QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C) (W V : Structure C)
  (hWE : W.cof ≤ E.inflation) (hEV : E.inflation ≤ V.cof) (n : SimplexCategory)

/-- The unit is the actual quotient by the zero initial object. -/
def flagCompletionUnit :
    𝟭 (WeakFlag W.cof V.weq n.len) ⟶
      completeFlags E W V hWE hEV ⋙ WeakRow.initialFlagFunctor where
  app F := ⟨(initialCompletionIso E F.diagram (fun f ↦ hWE _ (F.cofibration f)) F.zero).hom,
    fun _ ↦ V.weq_iso _ inferInstance⟩
  naturality F G α := by
    apply Subtype.ext
    ext i
    exact (flagQuotient_quotientNatTrans E
      (fun f ↦ hWE _ (F.cofibration f)) (fun f ↦ hWE _ (G.cofibration f))
      α.val (interval 0 i (Fin.zero_le _))).symm

/-- The counit identifies the chosen cokernel completion with the original
row, using its original cokernel universal property. -/
def rowCompletionCounit :
    WeakRow.initialFlagFunctor ⋙ completeFlags E W V hWE hEV ⟶
      𝟭 (WeakRow E W.cof V.weq n) where
  app F := ⟨(completedInitialIso E F.row).hom, fun _ ↦ V.weq_iso _ inferInstance⟩
  naturality F G α := by
    apply Subtype.ext
    ext p
    let : Epi (flagQuotient E (initialFlag E F.row) (initialFlag_inflation E F.row) p) :=
      inferInstance
    apply (cancel_epi (flagQuotient E (initialFlag E F.row) (initialFlag_inflation E F.row) p)).1
    change flagQuotient E _ _ p ≫
      ((quotientNatTrans E _ _ (Functor.whiskerLeft (initialIntervals n) α.val)).app p ≫
        (completedInitialIsoAt E G.row p).hom) =
      flagQuotient E _ _ p ≫ ((completedInitialIsoAt E F.row p).hom ≫ α.val.app p)
    rw [← Category.assoc, flagQuotient_quotientNatTrans, Category.assoc]
    have hF := flagQuotient_completedInitialIsoAt E F.row p
    have hG := flagQuotient_completedInitialIsoAt E G.row p
    simp only [initialFlag] at hG
    rw [hG, ← Category.assoc, hF]
    exact (α.val.naturality (homOfLE (show interval 0 p.1.2 (Fin.zero_le _) ≤ p from
      ⟨Fin.zero_le _, le_rfl⟩))).symm

/-- Actual initial-flag restriction is a homotopy equivalence on the nerves'
classifying spaces. Canonical cokernel completion supplies the inverse. -/
def rowInitialFlagClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (WeakRow E W.cof V.weq n))
      (ClassifyingSpace (WeakFlag W.cof V.weq n.len)) where
  toFun := (classifyingSpaceMap WeakRow.initialFlagFunctor).hom
  invFun := (classifyingSpaceMap (completeFlags E W V hWE hEV)).hom
  left_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
        classifyingSpaceNaturalTransformationHomotopy (rowCompletionCounit E W V hWE hEV n)⟩
  right_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
        (classifyingSpaceNaturalTransformationHomotopy (flagCompletionUnit E W V hWE hEV n)).symm⟩

@[simp]
theorem rowInitialFlagClassifyingHomotopyEquiv_toFun :
    (rowInitialFlagClassifyingHomotopyEquiv E W V hWE hEV n).toFun =
      (classifyingSpaceMap WeakRow.initialFlagFunctor).hom := rfl

end Quillen.Waldhausen
