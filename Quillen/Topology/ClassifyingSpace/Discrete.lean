/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyGroups.Discrete
public import Quillen.Topology.HomotopyGroups.WeakEquivalence
public import Quillen.CategoryTheory.TheoremB.TotalProjection
public import Quillen.Topology.Realization.TwoSidedBar.AugmentationEquivalence

/-!
# The original classifying space of a discrete category

An actual simplicial isomorphism and the constant-realization homeomorphism
identify the original realization with the discrete object space.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen

/-- The actual nerve realization of a discrete category is the discrete object space. -/
def discreteClassifyingIso (A : Type u) :
    ClassifyingSpace (Discrete A) ≅ TopCat.discrete.obj A :=
  SSet.toTop.mapIso (TwoSidedBar.discreteNerveIso A) ≪≫ TheoremB.constantRealizationIso A

/-- Every positive original homotopy group of a discrete category vanishes. -/
theorem discreteClassifying_subsingleton_pi (A : Type u)
    (x : ClassifyingSpace (Discrete A)) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (ClassifyingSpace (Discrete A)) x) := by
  let e := TopCat.homeoOfIso (discreteClassifyingIso A)
  let : Subsingleton (HomotopyGroup.Pi (n + 1) (TopCat.discrete.obj A)
      (e.toHomotopyEquiv.toFun x)) := subsingleton_positive_pi_of_discrete _ n
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv rfl
    (n + 1)).injective.subsingleton

end Quillen
